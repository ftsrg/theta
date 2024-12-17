## Overview

This package contains two new data structures, a Proof and a Cex.

### Abstract State Graph

`ASG` is a more simple state space representation than `ARG`. It works and is implemented in a very similar way,
except it does allow circles to appear in the graph.

### ASG trace

`ASGTrace` represents a lasso like trace, i.e. it is made with two parts: a tail and a loop. The loop is required
to start and end in the last state of the tail. This node in the graph is called honda.

### Visualization

The `ASGVisualizer` class (found in the `hu.bme.mit.theta.analysis.utils` package) provides visualization capabilities. Since it implements
the standard `ProofVisualizer` interface working on `ASG`s, the usage is fairly similar. Given an `ASG`, it returns a `hu.bme.mit.theta.common.visualization.Graph`
object that can be turned into actual visual representations (such as a Graphviz string with `hu.bme.mit.theta.common.visualization.writer.GraphvizWriter`
, which in turn can be displayed with external tools)