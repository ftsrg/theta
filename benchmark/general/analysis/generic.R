# Libraries ----------------------------------------------------------------------

library(tidyverse)
library(stringr)

# Common variables ---------------------------------------------------------------

csv_path = "../log_20170310_101235.csv" # Path of the data
timeout_ms = 10 * 60 * 1000 # Timeout used during the measurements


# Common themes ------------------------------------------------------------------
theme_rotate_x <- theme(axis.text.x = element_text(angle = 90, hjust = 1, vjust = 0.5))
theme_noticks <- theme(axis.ticks = element_blank())

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

# Create 'Config' column
d <- d %>% mutate(Config = paste(
  substr(d$Domain, 1, 1),
  substr(d$Refinement, 1, 1),
  substr(d$InitPrec, 1, 1),
  substr(d$Search, 1, 1),
  ifelse(is.na(d$PredSplit), "", substr(d$PredSplit, 1, 1)),
  sep = ""
))

# Trim name
d$Model <- as.factor(gsub("models/", "", d$Model))

# Separate 'Model' into 'Name' and 'Type'
d <- d %>% separate(Model, into = c("Type", "Name"), sep = "/", remove = F)


# Analysis -----------------------------------------------------------------------


# Heatmaps -----------------------------------------------------------------------

d_model_config <- d %>% group_by(Config, Model) %>%
  summarise(
    SafeCnt = sum(Safe, na.rm = T),
    SafeRatio = ifelse(SafeCnt == 0, 0, SafeCnt / sum(!is.na(Safe))),
    Consistent = near(SafeRatio, 1) || near(SafeRatio, 0),
    TimeAvg = mean(TimeMs),
    TimeRSD = sd(TimeMs) / mean(TimeMs))

ggplot(d_model_config, aes(Model, Config)) +
  geom_tile(aes(fill = Consistent), color = "black") +
  theme_noticks + theme_rotate_x

ggplot(d_model_config, aes(Model, Config)) +
  geom_tile(aes(fill = log(TimeAvg)), color = "black") +
  scale_fill_gradient(low = "green", high = "red", na.value = "white") +
  theme_noticks + theme_rotate_x
  