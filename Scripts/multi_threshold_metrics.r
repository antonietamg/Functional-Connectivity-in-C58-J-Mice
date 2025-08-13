###############################################################################
# Script: multi_threshold_metrics.R   (version 2025-08-13)
# Author: Antonieta Martínez-Guerrero et al. (see manuscript authorship)
#
# Purpose
#   Compute graph-theoretic metrics from individual functional connectivity
#   matrices under a hub-informed, multi-threshold scheme that separates
#   positive and negative networks. Results are saved as CSV tables and
#   overview plots suitable for supplementary materials.
#
# What this script does
#   • Cleans each matrix: removes rows/columns that are all-NA and nodes
#     labelled "unknown" (case-insensitive), then enforces symmetry.
#   • Applies 14 (N, p) threshold conditions per subject:
#       - Keep the top-N nodes by strength (sum of absolute weights) within
#         each polarity (positive / negative).
#       - Within that N-node subgraph, keep the top-p proportion of edge
#         weights (by absolute magnitude).
#   • Splits the matrix by correlation polarity (positive / negative) and
#     computes weighted metrics per condition and subject.
#   • Uses node strength as hubness criterion (i.e., top-N by strength).
#   • Converts weights to costs (1 / w) for shortest-path–based quantities.
#   • Computes a binary small-world index (σ) on the binarized graph derived
#     from the weighted adjacency (edges present if weight > 0).
#   • Computes cost-efficiency = GlobalEfficiency / Cost (Latora & Marchiori, 2001).
#   • Produces tidy CSV outputs and summary plots per polarity.
#
# Expected input
#   • A directory containing square CSV connectivity matrices (one per subject),
#     with the first column as row names and column names in the header. Values
#     are Pearson correlations in [-1, 1].
#
# Outputs
#   • Metrics_Positive.csv     – per-subject, per-condition metrics (positive)
#   • Metrics_Negative.csv     – per-subject, per-condition metrics (negative)
#   • Metrics_AllByCondition.csv – both polarities combined
#   • Plot_Positive_metrics.png – overview plot for positive networks
#   • Plot_Negative_metrics.png – overview plot for negative networks
#
# Reproducibility & usage
#   • Set a global random seed for reproducibility (defaults to 123).
#   • By default, the script reads matrices from ./data and writes results to
#     ./outputs (both relative to the working directory). You can override via
#     environment variables or command-line arguments.
#
# Quick start (from terminal)
#   Rscript multi_threshold_metrics.R
#   Rscript multi_threshold_metrics.R ./data ./outputs
#   Rscript multi_threshold_metrics.R ./data ./outputs 500 42
#
# Environment variables (optional)
#   DATA_DIR  – input directory (default: ./data)
#   OUTPUT_DIR – output directory (default: ./outputs)
#   NRAND     – number of random graphs for small-world index (default: 500)
#   SEED      – RNG seed (default: 123)
#
# Notes
#   • Positive and negative subnetworks are analyzed independently using
#     absolute weights after splitting by sign.
#   • If a condition yields an empty graph, metrics are reported as NA.
#   • Small-world index (σ) uses G(n, m) random graphs preserving n and m.
#
# References (for users; not fetched programmatically here)
#   Latora, V., & Marchiori, M. (2001). Efficient behavior of small-world
#   networks. Physical Review Letters, 87(19), 198701.
#   Humphries, M. D., & Gurney, K. (2008). Network 'small-world-ness': A
#   quantitative method for determining canonical network equivalence.
#   PLoS One, 3(4), e0002051.
###############################################################################

suppressPackageStartupMessages({
  library(igraph)
  library(tidyverse)
  library(progress)
  library(withr)
})

# ─────────────────────────────────────────────────────────────────────────────
# Configuration: paths, seed, and number of random graphs
# Priority: command-line args > environment variables > defaults
# ─────────────────────────────────────────────────────────────────────────────
args <- commandArgs(trailingOnly = TRUE)

get_arg_or <- function(i, env, default) {
  if (length(args) >= i && nzchar(args[[i]])) return(args[[i]])
  val <- Sys.getenv(env, unset = NA_character_)
  if (!is.na(val) && nzchar(val)) return(val)
  default
}

# Defaults are relative to current working directory
DATA_DIR   <- normalizePath(get_arg_or(1, "DATA_DIR",   "./data"), mustWork = FALSE)
OUTPUT_DIR <- normalizePath(get_arg_or(2, "OUTPUT_DIR", "./outputs"), mustWork = FALSE)
NRAND      <- as.integer(get_arg_or(3, "NRAND",        "500"))
SEED       <- as.integer(get_arg_or(4, "SEED",         "123"))

if (!dir.exists(DATA_DIR)) stop("Input directory not found: ", DATA_DIR)
dir.create(OUTPUT_DIR, showWarnings = FALSE, recursive = TRUE)
set.seed(SEED)

message("\n▶ multi_threshold_metrics.R running with:")
message("   DATA_DIR   = ", DATA_DIR)
message("   OUTPUT_DIR = ", OUTPUT_DIR)
message("   NRAND      = ", NRAND)
message("   SEED       = ", SEED, "\n")

# ─────────────────────────────────────────────────────────────────────────────
# Helper functions (metrics and utilities)
# ─────────────────────────────────────────────────────────────────────────────
# Distances using cost = 1/weight; zero-weight edges are absent in the graph
# so E(g)$weight should be strictly positive.
distances_inv <- function(g){
  w <- E(g)$weight
  if (length(w) == 0) return(matrix(Inf, nrow = vcount(g), ncol = vcount(g)))
  distances(g, weights = 1 / w)
}

global_efficiency <- function(g){
  n <- vcount(g)
  if (n <= 1) return(NA_real_)
  d   <- distances_inv(g)
  inv <- 1 / d;  inv[!is.finite(inv)] <- 0; diag(inv) <- 0
  sum(inv) / (n * (n - 1))
}

local_efficiency <- function(g){
  if (vcount(g) <= 2) return(NA_real_)
  mean(sapply(V(g), function(v){
    nb <- neighbors(g, v)
    if (length(nb) < 2) return(0)
    sg  <- induced_subgraph(g, nb)
    d   <- distances_inv(sg)
    inv <- 1 / d; inv[!is.finite(inv)] <- 0; diag(inv) <- 0
    n   <- vcount(sg)
    sum(inv) / (n * (n - 1))
  }))
}

small_world_index_bin <- function(g, nrand = 500){
  # Binarize: edge present if weight > 0
  A  <- as_adjacency_matrix(g, attr = "weight", sparse = FALSE)
  gB <- graph_from_adjacency_matrix((A > 0) + 0, mode = "undirected", diag = FALSE)
  if (vcount(gB) < 3L || gsize(gB) < 2L)
    return(c(gamma = NA_real_, lambda = NA_real_, sigma = NA_real_))

  Cr <- suppressWarnings(transitivity(gB, type = "global"))
  Lr <- suppressWarnings(mean_distance(gB, unconnected = TRUE))
  if (!is.finite(Cr) || !is.finite(Lr) || Lr == 0)
    return(c(gamma = NA_real_, lambda = NA_real_, sigma = NA_real_))

  Crn <- Lrn <- numeric(nrand)
  with_seed(SEED, {  # reproducible local seed
    for (i in seq_len(nrand)){
      gr     <- sample_gnm(vcount(gB), gsize(gB), directed = FALSE, loops = FALSE)
      Crn[i] <- suppressWarnings(transitivity(gr, type = "global"))
      Lrn[i] <- suppressWarnings(mean_distance(gr, unconnected = TRUE))
    }
  })
  Crn <- mean(Crn, na.rm = TRUE)
  Lrn <- mean(Lrn, na.rm = TRUE)
  if (!is.finite(Crn) || !is.finite(Lrn) || Crn == 0 || Lrn == 0)
    return(c(gamma = NA_real_, lambda = NA_real_, sigma = NA_real_))

  c(gamma  = Cr / Crn,
    lambda = Lr / Lrn,
    sigma  = (Cr / Crn) / (Lr / Lrn))
}

cost_and_costeff <- function(g, ge){
  cost <- edge_density(g, loops = FALSE)
  c(cost     = cost,
    cost_eff = ifelse(cost == 0, NA_real_, ge / cost))
}

degree_centralization <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  centr_degree(g, mode = "all", normalized = TRUE)$centralization
}

eigenvector_centrality_mean <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  out <- try(eigen_centrality(g, directed = FALSE, weights = E(g)$weight), silent = TRUE)
  if (inherits(out, "try-error")) NA_real_ else mean(out$vector)
}

kcore_info <- function(g){
  if (vcount(g) == 0) return(list(kcore_max = NA_integer_, nodes_kcore_max = ""))
  kc   <- coreness(g)
  kmax <- max(kc)
  list(kcore_max       = kmax,
       nodes_kcore_max = paste(V(g)$name[kc == kmax], collapse = ";"))
}

modularity_louvain  <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  tryCatch(modularity(cluster_louvain(g, weights = E(g)$weight)), error = \(e) NA_real_)
}

modularity_walktrap <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  tryCatch(modularity(cluster_walktrap(g, weights = E(g)$weight)), error = \(e) NA_real_)
}

graph_diameter <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  out <- try(diameter(g, directed = FALSE,
                      weights = ifelse(E(g)$weight == 0, NA, 1 / E(g)$weight)),
             silent = TRUE)
  if (inherits(out, "try-error")) NA_real_ else out
}

graph_avgpath  <- function(g){
  if (vcount(g) == 0) return(NA_real_)
  out <- try(mean_distance(g, directed = FALSE,
                           weights = ifelse(E(g)$weight == 0, NA, 1 / E(g)$weight),
                           unconnected = TRUE),
             silent = TRUE)
  if (inherits(out, "try-error")) NA_real_ else out
}

metrics_row <- function(g, subject_id, label, condition){
  if (vcount(g) == 0 || gsize(g) == 0){
    return(tibble(Subject              = subject_id,
                  NetworkType          = label,
                  Condition            = condition,
                  GlobalEfficiency     = NA_real_,
                  LocalEfficiency      = NA_real_,
                  SmallWorld_gamma     = NA_real_,
                  SmallWorld_lambda    = NA_real_,
                  SmallWorld_sigma     = NA_real_,
                  NetworkCost          = NA_real_,
                  CostEfficiency       = NA_real_,
                  DegreeCentralization = NA_real_,
                  EigenCentralityMean  = NA_real_,
                  KcoreMax             = NA_real_,
                  KcoreMaxNodes        = "",
                  Modularity_Louvain   = NA_real_,
                  Modularity_Walktrap  = NA_real_,
                  Diameter             = NA_real_,
                  AvgPathLength        = NA_real_))
  }

  ge <- global_efficiency(g)
  sw <- small_world_index_bin(g, NRAND)
  ce <- cost_and_costeff(g, ge)

  tibble(Subject              = subject_id,
         NetworkType          = label,
         Condition            = condition,
         GlobalEfficiency     = ge,
         LocalEfficiency      = local_efficiency(g),
         SmallWorld_gamma     = sw["gamma"],
         SmallWorld_lambda    = sw["lambda"],
         SmallWorld_sigma     = sw["sigma"],
         NetworkCost          = ce["cost"],
         CostEfficiency       = ce["cost_eff"],
         DegreeCentralization = degree_centralization(g),
         EigenCentralityMean  = eigenvector_centrality_mean(g),
         KcoreMax             = kcore_info(g)$kcore_max,
         KcoreMaxNodes        = kcore_info(g)$nodes_kcore_max,
         Modularity_Louvain   = modularity_louvain(g),
         Modularity_Walktrap  = modularity_walktrap(g),
         Diameter             = graph_diameter(g),
         AvgPathLength        = graph_avgpath(g))
}

# ─────────────────────────────────────────────────────────────────────────────
# Threshold grid: 7 values of N (top nodes by strength) and 7 of p (% edges)
# Combined as (N in {10,25,50,80,100,120,150} with p = 0.20) and
# (N = 50 with p in {0.05, 0.10, 0.20, 0.35, 0.50, 0.65, 0.85})
# → total 14 conditions
# ─────────────────────────────────────────────────────────────────────────────
grid_n <- c(10, 25, 50, 80, 100, 120, 150)
grid_p <- c(0.05, 0.10, 0.20, 0.35, 0.50, 0.65, 0.85)

levels_ordered <- c(sprintf("N%03d_P20", grid_n),
                    sprintf("N050_P%02d", round(grid_p * 100)))

cond_grid <- bind_rows(
  expand_grid(top_n = grid_n, top_percent = 0.20),
  expand_grid(top_n = 50,     top_percent = grid_p)
) |>
  distinct() |>
  mutate(Condition = sprintf("N%03d_P%02d", top_n, round(top_percent * 100)),
         Condition = factor(Condition, levels = unique(levels_ordered))) |>
  arrange(Condition)

# ─────────────────────────────────────────────────────────────────────────────
# Discover input files and initialize progress bar
# ─────────────────────────────────────────────────────────────────────────────
csv_files <- list.files(DATA_DIR, "\\.csv$", full.names = TRUE)
if (length(csv_files) == 0) stop("No CSV files found in ", DATA_DIR)

pb <- progress_bar$new(total = length(csv_files) * nrow(cond_grid),
                       format = "[:bar] :percent – ETA: :eta")

# ─────────────────────────────────────────────────────────────────────────────
# Main processing loop
# ─────────────────────────────────────────────────────────────────────────────
all_metrics <- map_dfr(csv_files, function(file){
  subject_id <- tools::file_path_sans_ext(basename(file))
  mat        <- as.matrix(read.csv(file, row.names = 1, check.names = FALSE))

  # Initial cleaning: drop all-NA rows/cols and any label containing 'unknown'
  all_na_row <- apply(mat, 1, \(x) all(is.na(x)))
  all_na_col <- apply(mat, 2, \(x) all(is.na(x)))
  unknown_r  <- grepl("unknown", rownames(mat), ignore.case = TRUE)
  unknown_c  <- grepl("unknown", colnames(mat), ignore.case = TRUE)
  valid_rows <- !(all_na_row | unknown_r)
  valid_cols <- !(all_na_col | unknown_c)
  nodes      <- intersect(rownames(mat)[valid_rows], colnames(mat)[valid_cols])
  mat        <- mat[nodes, nodes, drop = FALSE]
  mat[is.na(mat)] <- 0
  if (!isSymmetric(mat)) mat[lower.tri(mat)] <- t(mat)[lower.tri(mat)]

  # Iterate thresholds
  map_dfr(seq_len(nrow(cond_grid)), function(j){
    cond   <- cond_grid[j, ]
    top_n  <- cond$top_n
    top_p  <- cond$top_percent

    # Split by polarity and take absolute weights within each polarity
    P <- abs(replace(mat, mat < 0, 0))   # positive submatrix
    N <- abs(replace(mat, mat > 0, 0))   # negative submatrix

    res <- map2_dfr(list(P, N), c("Pos", "Neg"), function(M, label){
      strengths <- rowSums(M)
      top_n_eff <- min(top_n, length(strengths))
      if (top_n_eff < 1) return(metrics_row(make_empty_graph(), subject_id, label, cond$Condition))

      keep <- names(sort(strengths, decreasing = TRUE))[seq_len(top_n_eff)]
      M    <- M[keep, keep, drop = FALSE]

      upper_vals <- M[upper.tri(M)]
      if (length(upper_vals) == 0 || all(upper_vals == 0))
        return(metrics_row(make_empty_graph(), subject_id, label, cond$Condition))

      thr_idx <- max(1, floor(length(upper_vals) * top_p))
      thr_val <- sort(upper_vals, decreasing = TRUE)[thr_idx]
      M[M < thr_val] <- 0

      g <- graph_from_adjacency_matrix(M, mode = "undirected", weighted = TRUE, diag = FALSE)
      if (gsize(g) == 0) return(metrics_row(make_empty_graph(), subject_id, label, cond$Condition))

      metrics_row(g, subject_id, label, cond$Condition)
    })

    pb$tick()
    res
  })
})

# ─────────────────────────────────────────────────────────────────────────────
# Export CSVs
# ─────────────────────────────────────────────────────────────────────────────
positive <- filter(all_metrics, NetworkType == "Pos")
negative <- filter(all_metrics, NetworkType == "Neg")

write_csv(positive, file.path(OUTPUT_DIR, "Metrics_Positive.csv"))
write_csv(negative, file.path(OUTPUT_DIR, "Metrics_Negative.csv"))
write_csv(all_metrics, file.path(OUTPUT_DIR, "Metrics_AllByCondition.csv"))

cat("\n✔ All results written to:", OUTPUT_DIR, "\n")

# ─────────────────────────────────────────────────────────────────────────────
# Summary plots (per polarity)
# ─────────────────────────────────────────────────────────────────────────────
metrics_long <- all_metrics |>
  select(Subject, NetworkType, Condition, where(is.numeric)) |>
  mutate(Condition = factor(Condition, levels = levels(cond_grid$Condition))) |>
  pivot_longer(-c(Subject, NetworkType, Condition),
               names_to  = "Metric",
               values_to = "Value",
               values_drop_na = TRUE)

plot_save_net <- function(df, network_label, out_dir){
  if (nrow(df) == 0) return(invisible(NULL))
  p <- ggplot(df, aes(Condition, Value, group = Subject, colour = Subject)) +
    geom_line(alpha = 0.35, linewidth = 0.3) +
    geom_boxplot(aes(group = Condition), fill = NA, colour = "black",
                 width = 0.55, outlier.shape = NA) +
    facet_wrap(~ Metric, scales = "free_y", ncol = 4) +
    scale_x_discrete(drop = FALSE) +
    labs(title = paste("Metrics across threshold conditions –", network_label, "network"),
         x     = "Condition (N nodes – % edges)",
         y     = "Metric value") +
    theme_bw(base_size = 9) +
    theme(axis.text.x     = element_text(angle = 45, hjust = 1),
          legend.position = "none",
          panel.spacing   = unit(0.7, "lines"))

  ggsave(file.path(out_dir, paste0("Plot_", network_label, "_metrics.png")),
         p, width = 15, height = 8, dpi = 300)
}

plot_save_net(filter(metrics_long, NetworkType == "Pos"), "Positive", OUTPUT_DIR)
plot_save_net(filter(metrics_long, NetworkType == "Neg"), "Negative", OUTPUT_DIR)

message("✓ Plots saved in: ", OUTPUT_DIR)

# ─────────────────────────────────────────────────────────────────────────────
# Session info (useful for reproducibility in supplementary materials)
# ─────────────────────────────────────────────────────────────────────────────
si <- capture.output(sessionInfo())
writeLines(si, file.path(OUTPUT_DIR, "R_sessionInfo.txt"))
message("✓ Session info written to R_sessionInfo.txt")
