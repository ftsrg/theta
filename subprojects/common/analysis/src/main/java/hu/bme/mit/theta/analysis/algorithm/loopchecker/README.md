## Overview

This package provides algorithms that allow to look for accepting lasso shaped traces in a state space.
A lasso is a special form of trace, consisting of two parts: a tail and a loop. Both are like classic traces, where the
tail has to start from an initial state, and the loop has to start and end in the last state of the tail.
Loopchecker has to be provided with a predicate that can mark either states or actions as accepting. The loop checking
algorithms look for lasso traces that have such acceptance in their loop.

## Data structures

The data structures in Theta had a limitation that made them not suitable for the initial implementation of loopchecker.
Both ARG and Trace do not allow circles to appear in the state space. For this reason, loopchecker uses the
`hu.bme.mit.theta.analysis.algorithm.asg` package. The abstract state graph found in that package is suitable
for loop creation and detection, while the ASGTrace allows us to represent lasso shaped traces.

## Algorithms
For abstraction and trace concretization there are 2-2 algorithms, completely interchangeable. This is implemented
using the strategy design pattern.

### Abstraction

During abstraction, the `ASG` is built and explored until a valid `ASGTrace` is found. There are currently two algorithms
implemented, both based on a dept first search.

#### Nested Depth-First Search

NDFS contains of two Depth-First searches right after eachother to find a lasso trace. The goal of the first DFS
is to find any acceptance, and than the second should find the very same acceptance from there.

![]()


#### Guided depth first search

The basis of the
algorithm is Depth-First Search (DFS), where we do only one search with a modified
condition instead of two nested ones compared to NDFS. Let us call encountering an accepting state/transition an acceptance. In the DFS, while keeping an acceptance counter,
look for a node that is already on the stack and has a smaller value on the counter
than the top of the stack. 

![]()


### Concretization

Concretizing a lasso trace requires an extra step after simple concretization. First the lasso is straightened to a classic
trace, and a classic concretization is used to determine if it's even feasible. However, after that, one needs to make
sure that the loop of the lasso is also a possible loop in the concrete state space.

#### Milano

This is a more direct approach. It checks whether the honda can be in the same
state before and after the loop. This is done by adding the cycle validity constraint to the
loop. An expression is added to the solver that requires all variables to have the same value in the first and
last state of the loop. 

![]()

#### Bounded unrolling

The idea of bounded unwinding comes from E. Clarke et al., who defined an algorithm
to detect and refine lasso-shaped traces in the abstract state-space. The idea was that
even though we do not know if an abstract loop directly corresponds to a concrete loop,
we can be sure that the abstract loop can be concretized at most m different ways, where
m is the size of the smallest abstract state in the loop (if we think about abstract states as
sets of concrete states). That is because, if the loop is run m times and is concretizable,
the state that had the smallest number of concrete states has to repeat itself at least once.
The only limitations of the original algorithm were that it was defined for deterministic
operations only.

To slightly mitigate this limitation and be able to use the algorithm, we need to eliminate as many nondeterministic operations as possible. To achieve this, nondeterministic
operations have to be unfolded: they are replaced with all their possible deterministic
counterparts. For the nondet operations of `xsts`, this can be seen in the `XstsNormalizerPass` pass object. 

Another limitation of the original algorithm in our context is that Theta is working with
possibly infinite domains, for which m could also potentially evaluate to infinite. To have a
chance to avoid these infinite unwindings, it is worth noting that counting all the concrete
states allowed by the abstract states in the loop is an overapproximation of the number
of all possible different states the concrete loop can reach. If a variable is included in only
such assignments (or no assignments at all) where the expression contains only literals,
that variable has a fixed value throughout the loop. That means, for such variables, just
one unwinding is enough.

To find all the variables that contribute towards the needed number of unwindings, `VarCollectorStatementVisitor` is used.
![]()

Since infinite bounds can
still be encountered, there is a configurable maximum for the bound. If m would be greater
than that, the refiner falls back to the default concretizer algorithm, which is Milano in the current implementation.
