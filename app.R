# app.R
# Pickleball Scheduler + Rotating-Partner Points Tracker
#
# Key features:
# - Upload availability CSV: Name, Week01..WeekNN (0/1)
# - Schedule pods of 4; court per week = min(max_games, floor(available/4))
# - Fairness based on GamesPlayed / WeeksAvailable
# - Avoid repeat same-pod pairings via a penalty
# - Score entry: within each pod of 4, 3 rotating-partner matches
# - Scoring: team points scored (each player gets their team's points)
# - Lock completed games: once saved for (Week, Court), results are "Completed"
# - Protect against schedule changes: store pod in results, warn/block on mismatch
# - Regenerate schedule from a chosen week onward (freezes earlier weeks)
# - Upload/Download schedule/results for persistence (important for hosted apps)

library(shiny)

# --- Upload size limit (bytes) ---
# Default is small (~5MB), configurable via shiny.maxRequestSize. :contentReference[oaicite:1]{index=1}
options(shiny.maxRequestSize = 10 * 1024^2)  # 10 MB

# ----------------------------- Helpers -----------------------------

# Treat any non-Name column as a week column (Week01..WeekNN recommended)
is_week_col <- function(x) x != "Name"

# Safe "null coalescing"
`%||%` <- function(a, b) if (!is.null(a)) a else b

# Pair key for pair-count tracking
pair_key <- function(a, b) paste(sort(c(a, b)), collapse = "||")

# All 2-combinations of players in a pod (for "same pod" pairing penalty)
pairs_in_pod <- function(pod4) {
  combn(sort(pod4), 2, simplify = FALSE)
}

# Rotating partners for a pod of 4:
# p1+p2 vs p3+p4
# p1+p3 vs p2+p4
# p1+p4 vs p2+p3
pod_matches <- function(pod4) {
  stopifnot(length(pod4) == 4)
  p <- as.character(pod4)
  list(
    list(A = c(p[1], p[2]), B = c(p[3], p[4])),
    list(A = c(p[1], p[3]), B = c(p[2], p[4])),
    list(A = c(p[1], p[4]), B = c(p[2], p[3]))
  )
}

# Basic CSV validation (cheap but important)
validate_availability_df <- function(df) {
  if (!("Name" %in% names(df))) stop("Availability CSV must include a 'Name' column.")
  week_cols <- names(df)[sapply(names(df), is_week_col)]
  if (length(week_cols) == 0) stop("No week columns found.")
  # Coerce weeks to 0/1
  for (w in week_cols) {
    df[[w]] <- as.integer(df[[w]])
    df[[w]][is.na(df[[w]])] <- 0L
    df[[w]] <- ifelse(df[[w]] > 0, 1L, 0L)
  }
  # Names
  df$Name <- as.character(df$Name)
  if (anyDuplicated(df$Name)) stop("Duplicate names found in Name column. Names must be unique.")
  list(df = df, week_cols = week_cols)
}

# Compute played and pair_count from an existing (frozen) schedule
# schedule expected columns: Week, Court, P1,P2,P3,P4
compute_state_from_schedule <- function(schedule_df) {
  played <- list()
  pair_count <- list()
  
  if (is.null(schedule_df) || nrow(schedule_df) == 0) {
    return(list(played = played, pair_count = pair_count))
  }
  
  # Only games with pods (Game > 0)
  s <- schedule_df[schedule_df$Court > 0, , drop = FALSE]
  if (nrow(s) == 0) return(list(played = played, pair_count = pair_count))
  
  for (i in seq_len(nrow(s))) {
    pod <- c(s$P1[i], s$P2[i], s$P3[i], s$P4[i])
    pod <- pod[pod != ""]
    if (length(pod) != 4) next
    
    for (p in pod) {
      played[[p]] <- (played[[p]] %||% 0L) + 1L
    }
    for (pp in pairs_in_pod(pod)) {
      k <- pair_key(pp[1], pp[2])
      pair_count[[k]] <- (pair_count[[k]] %||% 0L) + 1L
    }
  }
  
  list(played = played, pair_count = pair_count)
}

generate_schedule <- function(df_avail,
                              max_games_per_week = 3,
                              restarts = 30,
                              lambda_pair = 3.0,
                              lambda_fair = 1.0,
                              lambda_target = 100.0,
                              seed = 1,
                              start_week = NULL,           # if provided, freeze weeks before it (based on column order)
                              frozen_schedule = NULL) {    # schedule rows for frozen weeks, if any
  
  set.seed(seed)
  
  v <- validate_availability_df(df_avail)
  df_avail <- v$df
  week_cols <- v$week_cols
  players <- as.character(df_avail$Name)
  
  # Total availability across the season (used for TargetGames floor and reporting)
  avail_total <- setNames(rowSums(df_avail[, week_cols, drop = FALSE]), players)
  
  # Minimum availability across players who are available at least once
  min_avail <- if (any(avail_total > 0)) min(avail_total[avail_total > 0]) else 0L
  
  # Everyone is pushed to play at least min_avail games, but never more than their availability
  target_games <- setNames(pmin(avail_total, min_avail), players)
  
  # Available players by week
  avail_by_week <- lapply(week_cols, function(w) players[df_avail[[w]] == 1L])
  names(avail_by_week) <- week_cols
  
  # Determine which weeks to schedule this run
  if (!is.null(start_week)) {
    if (!(start_week %in% week_cols)) stop("start_week not found among week columns.")
    idx <- match(start_week, week_cols)
    weeks_to_schedule <- week_cols[idx:length(week_cols)]
    weeks_frozen <- week_cols[1:(idx - 1)]
  } else {
    weeks_to_schedule <- week_cols
    weeks_frozen <- character(0)
  }
  
  # Use frozen schedule if provided; otherwise build an empty one
  frozen <- frozen_schedule
  if (is.null(frozen)) frozen <- data.frame()
  if (nrow(frozen) > 0) {
    # Keep only the frozen weeks (defensive)
    frozen <- frozen[frozen$Week %in% weeks_frozen, , drop = FALSE]
    # Ensure required columns exist
    need_cols <- c("Week","Court","P1","P2","P3","P4")
    miss <- setdiff(need_cols, names(frozen))
    if (length(miss) > 0) stop(paste("Frozen schedule missing columns:", paste(miss, collapse = ", ")))
  }
  
  # Baseline state from frozen schedule (so future schedule balances against already-played pods)
  base_state <- compute_state_from_schedule(frozen)
  base_played <- base_state$played
  base_pair_count <- base_state$pair_count
  
  # Score a candidate pod (lower is better)
  score_pod <- function(pod, played, pair_count) {
    # Fairness: prefer players with fewer TOTAL games played (NOT a ratio)
    gp <- sapply(pod, function(p) (played[[p]] %||% 0L))
    fairness <- sum(gp)
    
    # Pair repeats: penalize players being in same pod repeatedly
    pr <- 0
    for (pp in pairs_in_pod(pod)) {
      k <- pair_key(pp[1], pp[2])
      pr <- pr + (pair_count[[k]] %||% 0L)
    }
    
    # Target deficit bonus: choose players who still "owe" games to hit TargetGames
    deficits <- sapply(pod, function(p) {
      max(0L, target_games[[p]] - (played[[p]] %||% 0L))
    })
    target_bonus <- sum(deficits)  # more deficit => better to schedule them
    
    (lambda_fair * fairness) + (lambda_pair * pr) - (lambda_target * target_bonus)
  }
  
  best_obj <- Inf
  best_sched_remaining <- NULL
  best_state <- NULL
  
  for (r in seq_len(restarts)) {
    # Initialize played/pair_count from the frozen schedule baseline
    played <- base_played
    pair_count <- base_pair_count
    
    rows <- list()
    row_i <- 1L
    
    for (w in weeks_to_schedule) {
      avail <- avail_by_week[[w]]
      n_av <- length(avail)
      games <- min(max_games_per_week, floor(n_av / 4))
      
      # Random tie-breaking so restarts explore different schedules
      if (length(avail) > 1) avail <- sample(avail, length(avail), replace = FALSE)
      
      remaining <- avail
      pods <- list()
      
      for (g in seq_len(games)) {
        combos <- combn(remaining, 4, simplify = FALSE)
        if (length(combos) == 0) break
        
        scores <- vapply(combos, function(pod) {
          score_pod(pod, played, pair_count) + runif(1, 0, 1e-6)
        }, numeric(1))
        
        best_idx <- which.min(scores)
        pod <- as.character(combos[[best_idx]])
        pods[[g]] <- pod
        
        remaining <- setdiff(remaining, pod)
        
        # Update state
        for (p in pod) played[[p]] <- (played[[p]] %||% 0L) + 1L
        for (pp in pairs_in_pod(pod)) {
          k <- pair_key(pp[1], pp[2])
          pair_count[[k]] <- (pair_count[[k]] %||% 0L) + 1L
        }
      }
      
      scheduled <- unique(unlist(pods))
      sitout_available <- setdiff(avail_by_week[[w]], scheduled)
      unavailable <- setdiff(players, avail_by_week[[w]])
      
      if (length(pods) == 0) {
        rows[[row_i]] <- data.frame(
          Week = w, Court = 0L,
          P1 = "", P2 = "", P3 = "", P4 = "",
          SitOut_Available = paste(sitout_available, collapse = ", "),
          Unavailable = paste(unavailable, collapse = ", "),
          stringsAsFactors = FALSE
        )
        row_i <- row_i + 1L
      } else {
        for (g in seq_along(pods)) {
          pod <- pods[[g]]
          rows[[row_i]] <- data.frame(
            Week = w, Court = as.integer(g),
            P1 = pod[1], P2 = pod[2], P3 = pod[3], P4 = pod[4],
            SitOut_Available = paste(sitout_available, collapse = ", "),
            Unavailable = paste(unavailable, collapse = ", "),
            stringsAsFactors = FALSE
          )
          row_i <- row_i + 1L
        }
      }
    }
    
    sched_remaining <- do.call(rbind, rows)
    
    # Objective for this restart (season-level):
    # 1) meet TargetGames floor first
    # 2) then reduce spread in TOTAL games played
    # 3) then reduce repeated same-pod pairs
    
    played_full <- setNames(rep(0L, length(players)), players)
    for (p in players) played_full[[p]] <- (played[[p]] %||% 0L)
    
    unmet <- pmax(0L, target_games - played_full)
    target_obj <- sum(unmet)
    
    gp_all <- played_full[avail_total > 0]  # players available at least once
    fairness_obj <- if (length(gp_all) > 0) (max(gp_all) - min(gp_all)) else 0
    
    pc_vals <- unlist(pair_count)
    pair_obj <- if (length(pc_vals) > 0) sum(pmax(0, pc_vals - 1L)) else 0
    
    obj <- 10000 * target_obj + 10 * fairness_obj + 1 * pair_obj
    
    if (obj < best_obj) {
      best_obj <- obj
      best_sched_remaining <- sched_remaining
      best_state <- list(played = played, pair_count = pair_count)
    }
  }
  
  # Combine frozen + remaining schedules (if frozen exists)
  schedule <- if (nrow(frozen) > 0) {
    if (!("SitOut_Available" %in% names(frozen))) frozen$SitOut_Available <- ""
    if (!("Unavailable" %in% names(frozen))) frozen$Unavailable <- ""
    frozen <- frozen[, names(best_sched_remaining), drop = FALSE]
    rbind(frozen, best_sched_remaining)
  } else {
    best_sched_remaining
  }
  
  # Recompute summary and pair report from the final schedule
  state_final <- compute_state_from_schedule(schedule)
  played_final <- state_final$played
  pair_count_final <- state_final$pair_count
  
  games_played <- sapply(players, function(p) played_final[[p]] %||% 0L)
  weeks_avail <- as.integer(avail_total[players])
  ratio <- games_played / pmax(1L, weeks_avail)  # informational only
  
  summary <- data.frame(
    Name = players,
    WeeksAvailable = weeks_avail,
    GamesPlayed = as.integer(games_played),
    GamesPerAvailWeek = as.numeric(ratio),
    stringsAsFactors = FALSE
  )
  
  # Sort to reflect the new fairness intent: prioritize UnmetTarget, then total GamesPlayed
  summary <- summary[order(summary$GamesPlayed, summary$WeeksAvailable), ]
  
  pair_report <- data.frame(PlayerA = character(0), PlayerB = character(0), TimesSamePod = integer(0))
  if (length(pair_count_final) > 0) {
    keys <- names(pair_count_final)
    vals <- as.integer(unlist(pair_count_final))
    keep <- which(vals > 1L)
    if (length(keep) > 0) {
      key_keep <- keys[keep]
      vals_keep <- vals[keep]
      split_pairs <- strsplit(key_keep, "\\|\\|", fixed = FALSE)
      pair_report <- data.frame(
        PlayerA = vapply(split_pairs, `[`, "", 1),
        PlayerB = vapply(split_pairs, `[`, "", 2),
        TimesSamePod = vals_keep,
        stringsAsFactors = FALSE
      )
      pair_report <- pair_report[order(-pair_report$TimesSamePod), ]
    }
  }
  
  list(
    schedule = schedule,
    summary = summary,
    pair_report = pair_report,
    week_cols = week_cols
  )
}

# ----------------------------- UI -----------------------------

ui <- fluidPage(
  tags$head(
    tags$title("Pickleball League Organizer"),
    tags$link(rel = "icon", type = "image/png", href = "favicon.png?v=3")
  ),
  
  # visible header on the page
  tags$div(
    style = "display:flex; align-items:center; gap:10px; margin: 10px 0;",
    tags$img(src = "pickleball.png", style = "height:36px;"),
    tags$h2("Pickleball League Organizer", style = "margin:0;")
  ),
  
  tags$head(
    tags$style(HTML("
    /* Show a spinner whenever Shiny is busy */
    .shiny-busy-indicator {
      position: fixed;
      top: 12px;
      right: 12px;
      width: 26px;
      height: 26px;
      border: 4px solid rgba(0,0,0,0.15);
      border-top-color: rgba(0,0,0,0.6);
      border-radius: 50%;
      animation: spin 0.8s linear infinite;
      z-index: 9999;
      display: none;
    }
    .shiny-busy .shiny-busy-indicator { display: block; }
    @keyframes spin { to { transform: rotate(360deg); } }
    .shiny-busy .busy-dim { opacity: 0.5; pointer-events: none; }
  ")),
    tags$div(class = "shiny-busy-indicator")
  ),
  tabsetPanel(
    tabPanel("1) Upload & Schedule",
             sidebarLayout(
               sidebarPanel(
                 tags$h4("Instructions"),
                 tags$small("To make a new schedule, upload your availability csv file. (Format: Name, Date... with 1/0). 
                            If editing a schedule from an existing schedule, upload exisiting schedule and select which week to generate a new schedule from. 
                            This will use groupings from previous weeks to inform future groupings.
                            Ex./ If someone calls in sick or availability changes during the season."),
                 hr(),
                 tags$h4("Inputs"),
                 fileInput("avail_csv", "Upload availability CSV", accept = c(".csv")),
                 hr(),
                 tags$h4("Optional: load existing files"),
                 fileInput("schedule_csv", "Upload existing schedule.csv", accept = c(".csv")),
                 actionButton("load_files", "Load uploaded schedule"),
                 hr(),
                 tags$h4("Scheduling controls"),
                 tags$small("Maximum of 3 courts per week and scheduler tries 50 different iterations. Prioritizes playing a fair number of games, then making various groupings."),
                 hr(),
                 uiOutput("regen_week_ui"),
                 actionButton("make_schedule_full", "Generate full schedule", class = "btn-primary"),
                 actionButton("make_schedule_from", "Regenerate from selected week", class = "btn-warning"),
                 hr(),
                 tags$h4("Downloads"),
                 downloadButton("dl_schedule", "Download schedule.csv"),
                 downloadButton("dl_summary", "Download summary.csv"),
                 hr(),
                 tags$img(src = "schedule_meme.jpeg", style = "max-width:100%; border-radius:10px;")
               ),
               mainPanel(
                 tags$div(
                   class = "busy-dim",
                   tags$h4("Availability Counts & Games per Week"),
                   tableOutput("week_counts"),
                   hr(),
                   tags$h4("Schedule"),
                   tableOutput("schedule_table"),
                   hr(),
                   tags$h4("Summary Table"),
                   tableOutput("summary_table"),
                   hr(),
                   tags$h4("Pairings Counter"),
                   tableOutput("pair_table")
                 )
               )
             )
    ),
    
    tabPanel("2) Enter Scores",
             sidebarLayout(
               sidebarPanel(
                 uiOutput("week_picker"),
                 uiOutput("game_picker"),
                 checkboxInput("override_lock", "Override: allow overwriting a completed game", value = FALSE),
                 actionButton("save_scores", "Save Score", class = "btn-success"),
                 hr(),
                 tags$small("Tip: Reupload existing results and schedule to amend to the current results. Then dowload results.csv again to save since this does not keep memory."),
                 hr(),
                 tags$h4("Optional: Upload existing results file"),
                 fileInput("results_csv", "Load existing results file", accept = c(".csv")),
                 hr(),
                 tags$h4("Downloads"),
                 downloadButton("dl_results", "Download results.csv"),
                 hr(),
                 tags$img(src = "results_meme.jpeg", style = "max-width:100%; border-radius:10px;")
                 ),
               mainPanel(
                 tags$h4("Pod + rotating matches"),
                 uiOutput("score_entry_ui"),
                 hr(),
                 tags$h4("Saved results (preview)"),
                 tableOutput("results_preview")
               )
             )
    ),
    
    tabPanel("3) Leaderboard",
          sidebarLayout(
            sidebarPanel(
             tags$h4("Downloads"),
             downloadButton("dl_leaderboard", "Download leaderboard.csv"),
             hr(),
             tags$img(src = "champ_meme.png", style = "max-width:100%; border-radius:10px;")
            ),
            mainPanel(
             fluidRow(
               column(12,
                      tags$h4("Total points per player"),
                      tableOutput("leaderboard_table")
               )
             )
            ),
          )
    )
  )
)

# ----------------------------- Server -----------------------------

server <- function(input, output, session) {
  
  # Results schema:
  # Week, Court, Match,
  # PodSig, PodP1..PodP4 (stored pod to detect schedule changes),
  # A1,A2,B1,B2, ScoreA, ScoreB
  empty_results <- function() {
    data.frame(
      Week = character(0), Court = integer(0), Match = character(0),
      A1 = character(0), A2 = character(0), B1 = character(0), B2 = character(0),
      ScoreA = integer(0), ScoreB = integer(0),
      stringsAsFactors = FALSE
    )
  }
  
  rv <- reactiveValues(
    df_avail = NULL,
    schedule = NULL,
    summary = NULL,
    pair_report = NULL,
    results = empty_results()
  )
  
  # Load availability when uploaded
  observeEvent(input$avail_csv, {
    req(input$avail_csv)
    df <- read.csv(input$avail_csv$datapath, stringsAsFactors = FALSE, check.names = FALSE)
    # Validate/clean
    v <- validate_availability_df(df)
    rv$df_avail <- v$df
  })
  
  # Load schedule/results files if provided
  observeEvent(input$load_files, {
    # schedule
    if (!is.null(input$schedule_csv)) {
      s <- read.csv(input$schedule_csv$datapath, stringsAsFactors = FALSE, check.names = FALSE)
      # Expect columns Week, Court, P1..P4 at minimum
      need_cols <- c("Week","Court","P1","P2","P3","P4")
      miss <- setdiff(need_cols, names(s))
      if (length(miss) > 0) {
        showNotification(paste("schedule.csv missing columns:", paste(miss, collapse = ", ")), type = "error")
      } else {
        # Ensure correct types
        s$Week <- as.character(s$Week)
        s$Court <- as.integer(s$Court)
        for (cc in c("P1","P2","P3","P4","SitOut_Available","Unavailable")) {
          if (!(cc %in% names(s))) s[[cc]] <- ""
          s[[cc]] <- as.character(s[[cc]])
          s[[cc]][is.na(s[[cc]])] <- ""
        }
        rv$schedule <- s
        showNotification("Loaded schedule.csv", type = "message")
      }
    }
    
    # results
    if (!is.null(input$results_csv)) {
      r <- read.csv(input$results_csv$datapath, stringsAsFactors = FALSE, check.names = FALSE)
      
      need_cols <- c("Week","Court","Match","A1","A2","B1","B2","ScoreA","ScoreB")
      miss <- setdiff(need_cols, names(r))
      if (length(miss) > 0) {
        showNotification(paste("results.csv missing columns:", paste(miss, collapse = ", ")), type = "error")
      } else {
        r$Week <- as.character(r$Week)
        r$Court <- as.integer(r$Court)
        
        # Match can now be like "1.1" / "2.2" etc.
        r$Match <- as.character(r$Match)
        
        # Back-compat: if someone loads an old file with Match 1/2/3, map to 1.1/2.1/3.1
        if (all(r$Match %in% c("1","2","3")) && !any(grepl("\\.", r$Match))) {
          r$Match <- paste0(r$Match, ".1")
        }
        
        r$ScoreA <- as.integer(r$ScoreA)
        r$ScoreB <- as.integer(r$ScoreB)
        
        rv$results <- r
        showNotification("Loaded results.csv", type = "message")
      }
    }
  })
  
  # Week picker for regeneration (only if availability uploaded)
  output$regen_week_ui <- renderUI({
    req(rv$df_avail)
    if (is.null(rv$schedule) || nrow(rv$schedule) == 0) return(NULL)
  
    week_cols <- names(rv$df_avail)[sapply(names(rv$df_avail), is_week_col)]
    selectInput(
      "regen_from_week",
      "Regenerate starting at week",
      choices = week_cols,
      selected = week_cols[1]
    )
  })
  
  
  # Availability counts table
  output$week_counts <- renderTable({
    req(rv$df_avail)
    df <- rv$df_avail
    week_cols <- names(df)[sapply(names(df), is_week_col)]
    
    counts <- sapply(week_cols, function(w) sum(as.integer(df[[w]] > 0), na.rm = TRUE))
    
    max_games_per_week <- 3L
    
    data.frame(
      Week = week_cols,
      Available = as.integer(counts),
      GamesScheduled = pmin(max_games_per_week, floor(as.integer(counts) / 4)),
      stringsAsFactors = FALSE
    )
  }, striped = TRUE, bordered = TRUE, spacing = "s")
  
  observeEvent(input$make_schedule_full, {
    req(rv$df_avail)
    
    res <- generate_schedule(
      rv$df_avail,
      max_games_per_week = 3,
      restarts = 50,
      lambda_pair = 20,
      lambda_fair = 5,
      lambda_target = 100,
      seed = 1,
      start_week = NULL,
      frozen_schedule = NULL
    )
    
    rv$schedule <- res$schedule
    rv$summary <- res$summary
    rv$pair_report <- res$pair_report
    showNotification("Full schedule generated.", type = "message")
  })
  
  # Generate full schedule
  # Where you can change to inputs for sliders
  observeEvent(input$make_schedule_from, {
    req(rv$df_avail)
    req(input$regen_from_week)
    
    frozen <- NULL
    if (!is.null(rv$schedule) && nrow(rv$schedule) > 0) {
      frozen <- rv$schedule
    }
    
    res <- generate_schedule(
      rv$df_avail,
      max_games_per_week = 3,
      restarts = 50,
      lambda_pair = 20,
      lambda_fair = 5,
      lambda_target = 100,
      seed = 1,
      start_week = input$regen_from_week,
      frozen_schedule = frozen
    )
    
    if (nrow(rv$results) > 0) {
      completed_weeks <- unique(rv$results$Week)
      if (input$regen_from_week %in% completed_weeks) {
        showNotification(
          "Warning: you regenerated starting at a week that already has saved results. Completed games are locked; schedule/results mismatches will be blocked unless you override.",
          type = "warning", duration = 8
        )
      }
    }
    
    rv$schedule <- res$schedule
    rv$summary <- res$summary
    rv$pair_report <- res$pair_report
    showNotification(paste("Schedule regenerated from", input$regen_from_week), type = "message")
  })
  
  # Display schedule/summary/pair tables
  output$schedule_table <- renderTable({
    req(rv$schedule)
    rv$schedule
  }, striped = TRUE, bordered = TRUE, spacing = "s")
  
  output$summary_table <- renderTable({
    req(rv$summary)
    rv$summary
  }, striped = TRUE, bordered = TRUE, spacing = "s")
  
  output$pair_table <- renderTable({
    req(rv$pair_report)
    if (nrow(rv$pair_report) == 0) {
      data.frame(Note = "No pairs appeared together more than once in the same pod.")
    } else rv$pair_report
  }, striped = TRUE, bordered = TRUE, spacing = "s")
  
  # Downloads (schedule/summary/pairs/results)
  output$dl_schedule <- downloadHandler(
    filename = function() "schedule.csv",
    content = function(file) {
      req(rv$schedule)
      write.csv(rv$schedule, file, row.names = FALSE)
    }
  )
  output$dl_summary <- downloadHandler(
    filename = function() "summary.csv",
    content = function(file) {
      req(rv$summary)
      write.csv(rv$summary, file, row.names = FALSE)
    }
  )
  output$dl_pairs <- downloadHandler(
    filename = function() "pair_report.csv",
    content = function(file) {
      req(rv$pair_report)
      write.csv(rv$pair_report, file, row.names = FALSE)
    }
  )
  output$dl_results <- downloadHandler(
    filename = function() "results.csv",
    content = function(file) {
      write.csv(rv$results, file, row.names = FALSE)
    }
  )
  
  output$dl_leaderboard <- downloadHandler(
    filename = function() "leaderboard.csv",
    content = function(file) {
      req(rv$results)
      if (nrow(rv$results) == 0) {
        write.csv(data.frame(Player=character(0), MatchesPlayed=integer(0), TotalPoints=integer(0)),
                  file, row.names = FALSE)
        return()
      }
      
      totals <- list()
      matches  <- list()
      
      add_points <- function(player, pts) {
        if (is.na(player) || player == "") return()
        totals[[player]] <<- (totals[[player]] %||% 0L) + as.integer(pts)
      }
      add_match <- function(player) {
        if (is.na(player) || player == "") return()
        matches[[player]] <<- (matches[[player]] %||% 0L) + 1L
      }
      
      for (i in seq_len(nrow(rv$results))) {
        r <- rv$results[i, ]
        add_match(r$A1); add_match(r$A2); add_match(r$B1); add_match(r$B2)
        add_points(r$A1, r$ScoreA); add_points(r$A2, r$ScoreA)
        add_points(r$B1, r$ScoreB); add_points(r$B2, r$ScoreB)
      }
      
      players <- sort(unique(c(names(totals), names(matches))))
      
      df <- data.frame(
        Player = players,
        TotalPoints = as.integer(sapply(players, function(p) totals[[p]] %||% 0L)),
        MatchesPlayed = as.integer(sapply(players, function(p) matches[[p]] %||% 0L)),
        stringsAsFactors = FALSE
      )
      
      df <- df[order(-df$TotalPoints, -df$MatchesPlayed, df$Player), ]
      rownames(df) <- NULL
      write.csv(df, file, row.names = FALSE)
    }
  )
  
  
  # ---------------- Score entry ----------------
  
  output$week_picker <- renderUI({
    req(rv$schedule)
    weeks <- unique(rv$schedule$Week)
    selectInput("sel_week", "Week", choices = weeks)
  })
  
  output$game_picker <- renderUI({
    req(rv$schedule, input$sel_week)
    games <- rv$schedule$Court[rv$schedule$Week == input$sel_week]
    games <- sort(unique(games))
    games <- games[games > 0]
    if (length(games) == 0) {
      helpText("No games scheduled this week.")
    } else {
      selectInput("sel_game", "Court", choices = games)
    }
  })
  
  # Fetch current pod from schedule for selected week/game
  current_pod <- reactive({
    req(rv$schedule, input$sel_week, input$sel_game)
    row <- rv$schedule[rv$schedule$Week == input$sel_week & rv$schedule$Court == as.integer(input$sel_game), ]
    validate(need(nrow(row) == 1, "Could not find that week/court in schedule."))
    pod <- c(row$P1, row$P2, row$P3, row$P4)
    pod <- as.character(pod)
    pod[is.na(pod)] <- ""
    validate(need(all(nzchar(pod)), "This court has no pod assigned."))
    pod
  })
  
  # Determine if this game is completed (results exist)
  game_results <- reactive({
    req(input$sel_week)
    if (is.null(input$sel_game)) return(NULL)
    subset(rv$results, Week == input$sel_week & Court == as.integer(input$sel_game))
  })
  
  output$score_entry_ui <- renderUI({
    req(rv$schedule, input$sel_week)
    if (is.null(input$sel_game)) return(NULL)
    
    pod <- current_pod()
    matches <- pod_matches(pod)
    
    existing <- game_results()
    completed <- !is.null(existing) && nrow(existing) > 0
    
    # 6 entries: 1.1, 1.2, 2.1, 2.2, 3.1, 3.2
    labels <- as.vector(sapply(1:3, function(m) paste0(m, c(".1",".2"))))
    
    defaultA <- setNames(rep(0L, length(labels)), labels)
    defaultB <- setNames(rep(0L, length(labels)), labels)
    
    if (completed) {
      for (lab in labels) {
        rowm <- existing[as.character(existing$Match) == lab, , drop = FALSE]
        if (nrow(rowm) == 1) {
          defaultA[lab] <- as.integer(rowm$ScoreA)
          defaultB[lab] <- as.integer(rowm$ScoreB)
        }
      }
    }
    
    tagList(
      if (completed) {
        tags$div(
          tags$b("Status: Completed ✅ (locked by default)"),
          tags$br(),
          tags$small("To overwrite, check 'Override' on the left.")
        )
      },
      
      tags$p(tags$strong("Pod:"), paste(pod, collapse = ", ")),
      
      lapply(labels, function(lab) {
        base <- as.integer(strsplit(lab, "\\.", fixed = FALSE)[[1]][1])
        sub  <- as.integer(strsplit(lab, "\\.", fixed = FALSE)[[1]][2])
        
        A <- matches[[base]]$A
        B <- matches[[base]]$B
        
        idA <- paste0("scoreA_", base, "_", sub)  # e.g. scoreA_1_2
        idB <- paste0("scoreB_", base, "_", sub)
        
        fluidRow(
          column(
            5,
            tags$b(paste0("Match ", lab)),
            tags$div(paste0("Team A: ", paste(A, collapse = " + "))),
            tags$div(paste0("Team B: ", paste(B, collapse = " + ")))
          ),
          column(3, numericInput(idA, "Team A points", value = defaultA[lab], min = 0, step = 1)),
          column(3, numericInput(idB, "Team B points", value = defaultB[lab], min = 0, step = 1))
        )
      })
    )
  })
  
  observeEvent(input$save_scores, {
    req(rv$schedule, input$sel_week)
    if (is.null(input$sel_game)) return(NULL)
    
    week <- input$sel_week
    court <- as.integer(input$sel_game)
    
    pod <- current_pod()
    matches <- pod_matches(pod)
    
    existing <- subset(rv$results, Week == week & Court == court)
    completed <- nrow(existing) > 0
    
    # Enforce lock unless override checked
    if (completed && !isTRUE(input$override_lock)) {
      showNotification("This game is completed and locked. Check 'Override' to overwrite.", type = "error")
      return(NULL)
    }
    
    # Remove existing rows for this week/court (overwrite behavior)
    rv$results <- rv$results[!(rv$results$Week == week & rv$results$Court == court), , drop = FALSE]
    
    # Store pod players in results (so we can detect schedule changes later)
    pod_sorted <- sort(pod)
    
    labels <- as.vector(sapply(1:3, function(m) paste0(m, c(".1",".2"))))
    
    new_rows <- lapply(labels, function(lab) {
      base <- as.integer(strsplit(lab, "\\.", fixed = FALSE)[[1]][1])
      sub  <- as.integer(strsplit(lab, "\\.", fixed = FALSE)[[1]][2])
      
      A <- matches[[base]]$A
      B <- matches[[base]]$B
      
      idA <- paste0("scoreA_", base, "_", sub)
      idB <- paste0("scoreB_", base, "_", sub)
      
      data.frame(
        Week = week, Court = court, Match = lab,
        A1 = A[1], A2 = A[2], B1 = B[1], B2 = B[2],
        ScoreA = as.integer(input[[idA]]),
        ScoreB = as.integer(input[[idB]]),
        stringsAsFactors = FALSE
      )
    })
    
    rv$results <- rbind(rv$results, do.call(rbind, new_rows))
    showNotification("Scores saved/overwritten for this game.", type = "message")
  })
  
  output$results_preview <- renderTable({
    if (nrow(rv$results) == 0) return(data.frame(Note = "No results yet."))
    
    df <- rv$results
    df$Week <- as.character(df$Week)
    df$Court <- as.integer(df$Court)
    df$Match <- as.character(df$Match)
    
    # Sort by week/court and numeric match order (base, then sub)
    base <- suppressWarnings(as.integer(sub("\\..*$", "", df$Match)))
    subn <- suppressWarnings(as.integer(sub("^.*\\.", "", df$Match)))
    base[is.na(base)] <- 999L
    subn[is.na(subn)] <- 999L
    
    df <- df[order(df$Week, df$Court, base, subn), , drop = FALSE]
    
    out <- data.frame(
      Week = df$Week,
      Court = df$Court,
      `Match / Teams` = paste0(
        "<b>Match ", df$Match, "</b><br>",
        "Team A: ", df$A1, " + ", df$A2, "<br>",
        "Team B: ", df$B1, " + ", df$B2
      ),
      ScoreA = df$ScoreA,
      ScoreB = df$ScoreB,
      stringsAsFactors = FALSE
    )
    
    head(out, 30)
  }, striped = TRUE, bordered = TRUE, spacing = "s",
  sanitize.text.function = function(x) x)
  
  observeEvent(input$results_csv, {
    req(input$results_csv)
    
    r <- read.csv(input$results_csv$datapath, stringsAsFactors = FALSE, check.names = FALSE)
    
    need_cols <- c("Week","Court","Match","A1","A2","B1","B2","ScoreA","ScoreB")
    miss <- setdiff(need_cols, names(r))
    if (length(miss) > 0) {
      showNotification(paste("results.csv missing columns:", paste(miss, collapse = ", ")), type = "error")
      return()
    }
    
    r$Week  <- as.character(r$Week)
    r$Court <- as.integer(r$Court)
    r$Match <- as.character(r$Match)
    
    # Back-compat: Match 1/2/3 -> 1.1/2.1/3.1
    if (all(r$Match %in% c("1","2","3")) && !any(grepl("\\.", r$Match))) {
      r$Match <- paste0(r$Match, ".1")
    }
    
    r$ScoreA <- as.integer(r$ScoreA)
    r$ScoreB <- as.integer(r$ScoreB)
    
    rv$results <- r
    showNotification("Loaded results.csv", type = "message")
  })
  
  output$leaderboard_table <- renderTable({
    if (nrow(rv$results) == 0) return(data.frame(Note = "No results yet."))
    
    totals <- list()
    matches  <- list()
    
    add_points <- function(player, pts) {
      if (is.na(player) || player == "") return()
      totals[[player]] <<- (totals[[player]] %||% 0L) + as.integer(pts)
    }
    
    add_match <- function(player) {
      if (is.na(player) || player == "") return()
      matches[[player]] <<- (matches[[player]] %||% 0L) + 1L
    }
    
    for (i in seq_len(nrow(rv$results))) {
      r <- rv$results[i, ]
      
      # everyone in this row played one match
      add_match(r$A1); add_match(r$A2); add_match(r$B1); add_match(r$B2)
      
      # Team points scored: A1/A2 get ScoreA; B1/B2 get ScoreB
      add_points(r$A1, r$ScoreA); add_points(r$A2, r$ScoreA)
      add_points(r$B1, r$ScoreB); add_points(r$B2, r$ScoreB)
    }
    
    players <- sort(unique(c(names(totals), names(matches))))
    
    df <- data.frame(
      Player = players,
      TotalPoints = as.integer(sapply(players, function(p) totals[[p]] %||% 0L)),
      MatchesPlayed = as.integer(sapply(players, function(p) matches[[p]] %||% 0L)),
      stringsAsFactors = FALSE
    )
    
    # Sort: most points first, then most games played (tie-break)
    df <- df[order(-df$TotalPoints, -df$MatchesPlayed, df$Player), ]
    rownames(df) <- NULL
    df
  }, striped = TRUE, bordered = TRUE, spacing = "s")
}

shinyApp(ui, server)

