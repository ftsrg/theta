library(ggplot2)
library(iplots)
library(dplyr)
library(partykit)
library(corrgram)
library(reshape)
library(lubridate)
library(reproducer)
library(gridExtra)

timeout.ms <- 480000                           # Timeout, which was used during the measurements
csv.path = "log_20161209_153530_hw_plc_vm.csv" # Path of the data

d <- read.csv(csv.path, header=T, sep=",", quote="", na.strings="")
# Formatting: trim the name of the model, determine new variable 'Type'
d$Model <- as.factor(gsub("models/", "", d$Model))
d$Model <- as.factor(substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1))
d <- data.frame(Type = as.factor(substr(d$Model, 0, regexpr('/', d$Model) - 1)), d)
# Filter timeouts
d.no.to <- d %>% filter(!is.na(TimeMs))
# Check column types
str(d)
# Check summary values
summary(d)
d.succ <- data.frame(d, Success = ifelse(!is.na(d$TimeMs), "SUCC", "TO") )
tree <- ctree(Success ~ Type + Domain + Refinement + InitPrec + Search, data = d.succ)
plot(tree, tp_args = list(fill = c("red", "green")))

# Simple plots
qplot(data=d, Domain, TimeMs, geom="boxplot")
qplot(data=d, Refinement, TimeMs, color=Domain) + facet_wrap(~Model)
qplot(data=d, Refinement, TimeMs, color=Type) + facet_wrap(~Domain) + scale_y_log10()
ggplot(d, aes(ARGdepth, CEXlen, color=Type)) + geom_point() 
ggplot(d.corr, aes(TimeMs, Iterations)) + geom_point(alpha=1/5) 
ggplot(d, aes(ARGsize, Vars, color=Type)) + geom_point(alpha=1/5) + scale_x_log10()
