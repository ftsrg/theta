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

d.cex <- d %>% filter(!is.na(CEXlen))
tree <- ctree(CEXlen ~ Type + Domain + Refinement + InitPrec + Search, data = d.cex)
plot(tree, type = "simple", gp = gpar(fontsize = 8))


d.cex.sel <- select(d.cex, Model, Domain, Refinement, InitPrec, Search, CEXlen)
d.cex.test <- inner_join(filter(d.cex.sel, Search == "BFS"), filter(d.cex.sel, Search == "DFS"), by = c("Model", "Domain", "Refinement", "InitPrec"))

wilcox.test(d.cex.test$CEXlen.x, d.cex.test$CEXlen.y, paired = TRUE)

wilcox.test(CEXlen ~ Search, data=d.cex) 

qplot(d.cex.test$CEXlen.x, geom = "histogram")
qplot(d.cex.test$CEXlen.y, geom = "histogram")

# Simple plots
qplot(data=d, Domain, TimeMs, geom="boxplot")
qplot(data=d, Refinement, TimeMs, color=Domain) + facet_wrap(~Model)
qplot(data=d, Refinement, TimeMs, color=Type) + facet_wrap(~Domain) + scale_y_log10()
ggplot(d, aes(Vars, Size, color=Type)) + geom_point() 
ggplot(d.corr, aes(TimeMs, Iterations)) + geom_point(alpha=1/5) 
ggplot(d, aes(ARGsize, Vars, color=Type)) + geom_point(alpha=1/5) + scale_x_log10()
