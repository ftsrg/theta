library(ggplot2)
library(iplots)
library(dplyr)

# Load data
d <- read.csv("../results/log_20161206_154049_hw_vm.csv", header=T, sep=",", quote="", na.strings="")

# Add column 'Type' based on the path of the model
d$Type <- substr(d$Model, 0, regexpr('/', d$Model) - 1)
# Remove extension
d$Model <- substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1)

# Check column types
str(d)
# Check summary values
summary(d)

# Interactive stuff with iPlots
ibar(d$Domain)
iplot(d$Iterations, d$TimeMs)

# Plots
qplot(data=d, Domain, TimeMs, geom="boxplot")
qplot(data=d, Refinement, TimeMs, color=Domain) + facet_wrap(~Model)

ggplot(d, aes(TimeMs, ARGsize, color=Domain)) + geom_point() + scale_y_log10() + scale_x_log10()

d.pred <- select(filter(d, Domain=="PRED"), Model, Domain, Refinement, InitPrec, Search, TimeMs)
d.expl <- select(filter(d, Domain=="EXPL"), Model, Domain, Refinement, InitPrec, Search, TimeMs)
d.join <- inner_join(d.pred, d.expl, by=c("Model", "Refinement", "InitPrec", "Search"))
ggplot(d.join, aes(TimeMs.x, TimeMs.y)) + geom_point() + scale_y_log10() + scale_x_log10()
