library(ggplot2)
library(dplyr)
library(partykit)
library(gridExtra)

# Common variables
timeout.ms <- 480000                           # Timeout used during the measurements
csv.path = "log_20161209_153530_hw_plc_vm.csv" # Path of the data

# Load and clean data
d <- read.csv(csv.path, header = T, sep = ",", quote = "", na.strings = "")
# Formatting: trim the name of the model
d$Model <- as.factor(gsub("models/", "", d$Model))
d$Model <- as.factor(substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1))
# Determine new variable 'Type' from the model name
d <- data.frame(Type = as.factor(substr(d$Model, 0, regexpr('/', d$Model) - 1)), d)
# Remove plc from the beginning of "plc/plcX"
d$Model <- as.factor(gsub("plc/", "", d$Model))
# Give a short name to hardware models
hw.names = lapply(unique(d %>% filter(Type == "hw") %>% select(Model))$Model, as.character)
hw.short = paste("hw", 1:length(hw.names), sep = "")
for (i in 0:length(hw.names)) {
  levels(d$Model)[levels(d$Model) == hw.names[i]] <- hw.short[i]
}
# Shorten refinements
d$Refinement <- as.factor(gsub("CRAIG_ITP", "CRAIGI", d$Refinement))
d$Refinement <- as.factor(gsub("SEQ_ITP", "SEQI", d$Refinement))
d$Refinement <- as.factor(gsub("UNSAT_CORE", "UNSC", d$Refinement))

# Determine a new variable 'Conf'
d$Config <- as.factor(paste(substring(d$Domain, 1, 1),
                          substring(d$Refinement, 1, 1),
                          substring(d$InitPrec, 1, 1),
                          substring(d$Search, 1, 1),
                          sep = ""))
# Filter timeouts
d.no.to <- d %>% filter(!is.na(TimeMs))
d.cex <- d %>% filter(!is.na(CEXlen))

# High level overview

# Descriptive statistics
length(unique(d$Model)) # Number of models
nrow(unique(select(d, Domain, Refinement, InitPrec, Search))) # Number of configurations
str(d) # Check column types
summary(d) # Check summary values


grid.arrange(
  qplot(d.no.to$Safe, xlab = "Safe"),
  qplot(d.no.to$TimeMs, geom = "histogram", bins = 10, xlab = "TimeMs"),
  qplot(d.no.to$Iterations, geom = "histogram", bins = 10, xlab = "Iterations"),
  qplot(d.no.to$ARGsize, geom = "histogram", bins = 10, xlab = "ARGsize"),
  qplot(d.no.to$ARGdepth, geom = "histogram", bins = 10, xlab = "ARGdepth"),
  qplot(filter(d.no.to, !is.na(d.no.to$CEXlen))$CEXlen, geom = "histogram", bins = 20, xlab = "CEXlen")
)

grid.arrange(
  qplot(d.no.to$Safe, xlab = "", ylab = "Safe") + theme_bw() + theme(axis.text.x=element_text(angle=90,hjust=1,vjust=0.5)),
  ggplot(d.no.to, aes("TimeMs", TimeMs), main="") + geom_boxplot() + theme_bw() + theme(axis.title.x=element_blank(), axis.text.x=element_blank(), axis.ticks.x=element_blank()),
  ggplot(d.no.to, aes("Iterations", Iterations)) + geom_boxplot() + theme_bw() + theme(axis.title.x=element_blank(), axis.text.x=element_blank(), axis.ticks.x=element_blank()),
  ggplot(d.no.to, aes("ARGsize", ARGsize)) + geom_boxplot() + theme_bw() + theme(axis.title.x=element_blank(), axis.text.x=element_blank(), axis.ticks.x=element_blank()),
  ggplot(d.no.to, aes("ARGdepth", ARGdepth)) + geom_boxplot() + theme_bw() + theme(axis.title.x=element_blank(), axis.text.x=element_blank(), axis.ticks.x=element_blank()),
  ggplot(d.no.to, aes("CEXlen", CEXlen)) + geom_boxplot() + theme_bw() + theme(axis.title.x=element_blank(), axis.text.x=element_blank(), axis.ticks.x=element_blank()),
  nrow = 1
)




# Calculate average execution time and RSD for each configuration and model
model.conf.time <- d %>% group_by(Config, Model) %>%
  summarise(Tavg = log10(mean(TimeMs)), RSD = sd(TimeMs)/mean(TimeMs))
# Plot average time
ggplot(model.conf.time, aes(Model, Config, fill = Tavg)) +
  geom_tile(colour = "black") +
  scale_fill_gradient(low = "green", high = "red", na.value = "white") +
  labs(x = "Model", y = "Configuration") +
  theme_bw() +
  theme(axis.text.x = element_text(angle = 90, hjust = 1, vjust = 0.5), axis.ticks = element_blank())

# RSD
max(model.conf.time$RSD, na.rm = TRUE)

# Linear regression
# Iterations ~ Time (PLC)
d.corr.plc.no.to <- filter(d.no.to, !is.na(TimeMs) & Type == "plc")
ggplot(d.corr.plc.no.to, aes(Iterations, TimeMs)) +
  geom_point(alpha = 1/5, size = 3) +
  labs(x = "Iterations", y = "Time") +
  geom_smooth(method = "lm")

summary(lm(d.corr.plc.no.to$TimeMs ~ d.corr.plc.no.to$Iterations))

# Pairwise

# Domain vs execution time

# Select only input variables and time
d.inputs.time <- select(d, Type, Model, Domain, Refinement, InitPrec, Search, TimeMs)
# Fill NAs with timeout value
d.inputs.time[is.na(d.inputs.time)] <- timeout.ms
# Filter for the different domains and join by the other columns
d.domain.time <- inner_join(
  filter(d.inputs.time, Domain == "PRED"),
  filter(d.inputs.time, Domain == "EXPL"),
  by = c("Type", "Model", "Refinement", "InitPrec", "Search"))
# Filter where both times are timeout
d.domain.time <- filter(d.domain.time, TimeMs.x !=  timeout.ms | TimeMs.y !=  timeout.ms)

# Plot
ggplot(d.domain.time, aes(TimeMs.x, TimeMs.y, color = Type)) +
  scale_y_log10() + scale_x_log10() +
  geom_bin2d(binwidth = 0.25) +
  scale_fill_gradient(low = "gray", high = "black") + 
  geom_point(alpha = 1, size = 2) +
  geom_abline() +
  labs(x = "PRED", y = "EXPL") +
  theme_bw() +
  theme(panel.grid.major = element_line(colour = "darkgray"))
  

# Refinement vs iterations

# Select only input variables and iterations
d.inputs.iters <- select(d, Type, Model, Domain, Refinement,
                         InitPrec, Search, Iterations)
d.inputs.iters <- filter(d.inputs.iters, !is.na(Iterations))
# Filter for the different refinements and join by the other columns
d.refin.iters <- inner_join(
  filter(d.inputs.iters, Refinement == "CRAIGI"),
  filter(d.inputs.iters, Refinement == "SEQI"),
  by = c("Type", "Model", "Domain", "InitPrec", "Search"))

# Plot
ggplot(d.refin.iters, aes(Iterations.x, Iterations.y, color = Type)) +
  geom_bin2d(binwidth = 2.5) +
  scale_fill_gradient(low = "gray", high = "black") + 
  geom_point(alpha = 1, size = 2) +
  geom_abline() +
  labs(x = "CRAIGI", y = "SEQI") +
  theme_bw() +
  theme(panel.grid.major = element_line(colour = "darkgray"))

# Decision tree
d.succ <- data.frame(d, Success = ifelse(!is.na(d$TimeMs), "SUCC", "TO") )
# Generate tree
tree <- ctree(Success ~ Type + Domain + Refinement + InitPrec + Search, data = d.succ)
plot(tree, tp_args = list(fill = c("red", "green3"), id = FALSE), ip_args = list(id = FALSE, pval = FALSE))
