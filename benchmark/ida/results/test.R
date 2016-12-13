library(ggplot2)
library(iplots)
library(dplyr)
library(party)
library(corrgram)

timeout.ms <- 480000                           # Timeout, which was used during the measurements
csv.path = "log_20161209_153530_hw_plc_vm.csv" # Path of the data

d <- read.csv(csv.path, header=T, sep=",", quote="", na.strings="")
# Filter timeouts
d.no.to <- d %>% filter(!is.na(TimeMs))
# Formatting: trim the name of the model, determine new variable 'Type'
d$Model <- as.factor(gsub("models/", "", d$Model))
d$Model <- as.factor(substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1))
d <- data.frame(Type = as.factor(substr(d$Model, 0, regexpr('/', d$Model) - 1)), d)
# Check column types
str(d)
# Check summary values
summary(d)

View( d.no.to %>% group_by(Model, Domain, Refinement, InitPrec, Search, Type) %>% summarise( sd(TimeMs, na.rm = TRUE) ))

d.corr <- select(d, TimeMs, Vars, Iterations, ARGsize, ARGdepth, CEXlen)
cor(d.corr, use="pairwise.complete.obs")
corrgram(d.corr, order=TRUE, lower.panel = panel.shade, upper.panel = panel.pie)
corrgram(d.corr, order=TRUE, lower.panel = panel.ellipse, upper.panel = panel.pts)

# Interactive stuff with iPlots
#ibar(d$Domain)
#iplot(d$Iterations, d$TimeMs)

# Simple plots
qplot(data=d, Domain, TimeMs, geom="boxplot")
qplot(data=d, Refinement, TimeMs, color=Domain) + facet_wrap(~Model)
qplot(data=d, Refinement, TimeMs, color=Type) + facet_wrap(~Domain) + scale_y_log10()
ggplot(d, aes(TimeMs, ARGsize, color=Type)) + geom_point() + scale_y_log10() + scale_x_log10()
ggplot(d.corr, aes(TimeMs, Iterations)) + geom_point(alpha=1/5) 
ggplot(d, aes(ARGsize, Vars, color=Type)) + geom_point(alpha=1/5) + scale_x_log10()
