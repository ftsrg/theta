library(ggplot2)
library(iplots)
library(dplyr)
library(party)

timeoutMs <- 480000

# Load data
d <- read.csv("../results/log_20161209_153530_hw_plc_vm.csv", header=T, sep=",", quote="", na.strings="")

# Add column 'Type' based on the path of the model
d$Model <- as.factor(gsub("models/", "", d$Model))
d$Type <- as.factor(substr(d$Model, 0, regexpr('/', d$Model) - 1))
# Remove extension
d$Model <- as.factor(substr(d$Model, 0, regexpr("\\.[^\\.]*$", d$Model) - 1))

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
ggplot(d, aes(TimeMs, Iterations, color=Domain)) + geom_point(alpha=1/5) + scale_x_log10()

# Advanced plots

# Joined scatterplots for two factors of a configuration variable (where rest of the configuration is the same)
d.selected <- select(d, Type, Model, Domain, Refinement, InitPrec, Search, TimeMs)
d.selected[is.na(d.selected)] <- timeoutMs

d.join <- inner_join(filter(d.selected, Domain=="PRED"), filter(d.selected, Domain=="EXPL"), by=c("Model", "Refinement", "InitPrec", "Search"))
#d.join <- inner_join(filter(d.selected, Search=="BFS"), filter(d.selected, Search=="DFS"), by=c("Model", "Refinement", "InitPrec", "Domain"))
#d.join <- inner_join(filter(d.selected, InitPrec=="EMPTY"), filter(d.selected, InitPrec=="PROP"), by=c("Model", "Refinement", "Search", "Domain"))
#d.join <- inner_join(filter(d.selected, Refinement=="CRAIG_ITP"), filter(d.selected, Refinement=="SEQ_ITP"), by=c("Model", "InitPrec", "Search", "Domain"))

# Filter where both times are timeout
d.join <- filter(d.join, TimeMs.x != timeoutMs | TimeMs.y != timeoutMs)

# Heatmap
ggplot(d.join, aes(TimeMs.x, TimeMs.y, color=Type.x)) + scale_y_log10() + scale_x_log10() +
  geom_bin2d(bins=14) + scale_fill_gradient(low = "green", high = "red") + 
  geom_point(alpha=1/20, size=3) +
  geom_abline()
  #labs(title = "Runtime of different domains", x = "Pred", y = "Expl")


# Clustering
d.cluster <- scale(select(d.join, TimeMs.x, TimeMs.y))
# Determine number of clusters
wss <- (nrow(d.cluster)-1)*sum(apply(d.cluster,2,var))
for (i in 2:15) wss[i] <- sum(kmeans(d.cluster,centers=i)$withinss)
plot(1:15, wss, type="b", xlab="Number of Clusters", ylab="Within groups sum of squares") 

# K-Means Cluster Analysis
fit <- kmeans(d.cluster, 3)
# get cluster means
aggregate(d.cluster,by=list(fit$cluster),FUN=mean)
# append cluster assignment
d.cluster <- data.frame(d.cluster, fit$cluster)

# Decision tree
d.no.to <- d %>% filter(! is.na(TimeMs))
str(d.no.to)
tree <- ctree(  TimeMs ~ Type  + Domain + Refinement + InitPrec + Search, data = d.no.to)
plot(tree)