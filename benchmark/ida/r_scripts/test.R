library(ggplot2)
library(iplots)
library(dplyr)
library(party)

# Load data
d <- read.csv("../results/log_20161206_154049_hw_vm.csv", header=T, sep=",", quote="", na.strings="")

# Add column 'Type' based on the path of the model
d$Type <- substr(d$Model, 0, regexpr('/', d$Model) - 1)
# Remove extension
#d$Model <- substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1)

# Check column types
str(d)
# Check summary values
summary(d)

# Interactive stuff with iPlots
ibar(d$Domain)
iplot(d$Iterations, d$TimeMs)

# Simple plots
qplot(data=d, Domain, TimeMs, geom="boxplot")
qplot(data=d, Refinement, TimeMs, color=Domain) + facet_wrap(~Model)
ggplot(d, aes(TimeMs, ARGsize, color=Domain)) + geom_point() + scale_y_log10() + scale_x_log10()

# Advanced plots

# Joined scatterplots for two factors of a configuration variable (where rest of the configuration is the same)
d.selected <- select(d, Model, Domain, Refinement, InitPrec, Search, TimeMs)
d.selected[is.na(d.selected)] <- 600000

d.join <- inner_join(filter(d.selected, Domain=="PRED"), filter(d.selected, Domain=="EXPL"), by=c("Model", "Refinement", "InitPrec", "Search"))
d.join <- inner_join(filter(d.selected, Search=="BFS"), filter(d.selected, Search=="DFS"), by=c("Model", "Refinement", "InitPrec", "Domain"))
d.join <- inner_join(filter(d.selected, InitPrec=="EMPTY"), filter(d.selected, InitPrec=="PROP"), by=c("Model", "Refinement", "Search", "Domain"))
d.join <- inner_join(filter(d.selected, Refinement=="CRAIG_ITP"), filter(d.selected, Refinement=="SEQ_ITP"), by=c("Model", "InitPrec", "Search", "Domain"))

# Heatmap
ggplot(d.join, aes(TimeMs.x, TimeMs.y)) + scale_y_log10() + scale_x_log10() +
  geom_bin2d(bins=14) + scale_fill_gradient(low = "green", high = "red") + 
  geom_point(alpha=1/2, size=3) +
  geom_abline()
  #labs(title = "Runtime of different domains", x = "Pred", y = "Expl")

# Decision tree
d.no.to <- d %>% filter(! is.na(TimeMs))
str(d.no.to)
tree <- ctree(  TimeMs ~ Model + Domain + Refinement + InitPrec + Search, data = d.no.to)
plot(tree)