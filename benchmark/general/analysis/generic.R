# Libraries ----------------------------------------------------------------------

library(tidyverse)
library(stringr)

# Common variables ---------------------------------------------------------------

csv_path = "../log_20170310_101235.csv" # Path of the data
timeout_ms = 10 * 60 * 1000 # Timeout used during the measurements

# Read data ----------------------------------------------------------------------

d <- read_csv(
  csv_path,
  col_types = cols(
    Model = col_character(),
    Vars = col_integer(),
    Size = col_integer(),
    Domain = col_character(),
    Refinement = col_character(),
    InitPrec = col_character(),
    Search = col_character(),
    PredSplit = col_character(),
    Safe = col_character(),
    TimeMs = col_integer(),
    Iterations = col_integer(),
    ArgSize = col_integer(),
    ArgDepth = col_integer(),
    CexLen = col_integer()
  )
)

# Clean data ---------------------------------------------------------------------

# Create factors
d$Domain <- factor(d$Domain)
d$Refinement <- factor(d$Refinement)
d$InitPrec <- factor(d$InitPrec)
d$Search <- factor(d$Search)
d$PredSplit <- factor(d$PredSplit)

# Convert 'Safe' to logical (and remove exceptions)
ex_rows <- str_detect(d$Safe, "\\[EX\\]")
exs <- sum(ex_rows, na.rm = T)
if (exs > 0) warning(paste(c(exs, " rows contain exceptions that are converted to NAs.")))
d$Safe <- as.logical(d$Safe)