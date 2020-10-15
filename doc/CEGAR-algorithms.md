# CEGAR algorithms

Most of the tools in Theta employ variants of counterexample-guided abstraction refinement (CEGAR) algorithms.
This document gives a brief introduction to the possible configuration options of the algorithm, including best practices.

## CEGAR in general


> "[Counterexample-Guided Abstraction Refinement](https://link.springer.com/chapter/10.1007/10722167_15) (CEGAR) is a widely used technique for the automated formal verification of different systems, including both software and hardware.
CEGAR works by iteratively constructing and refining abstractions until a proper precision is reached.
It starts with computing an abstraction of the system with respect to some abstract domain and a given initial -- usually coarse -- precision.
The abstraction [over-approximates](https://dl.acm.org/doi/10.1145/186025.186051) the possible behaviors (i.e., the state space) of the original system.
Thus, if no erroneous behavior can be found in the abstract state space then the original system is also safe.
However, abstract counterexamples corresponding to erroneous behaviors must be checked whether they are reproducible (feasible) in the original system.
A feasible counterexample indicates that the original system is unsafe.
Otherwise, the counterexample is spurious and it is excluded in the next iteration by adjusting the precision to build a finer abstraction.
The algorithm iterates between abstraction and refinement until the abstract system is proved safe, or a feasible counterexample is found.

> CEGAR is a generic approach with many variants developed over the past two decades, improving both applicability and performance.
There are different abstract domains, including [predicates](https://link.springer.com/chapter/10.1007/3-540-63166-6_10) and [explicit values](https://link.springer.com/chapter/10.1007/978-3-642-37057-1_11) and various refinement strategies, including ones based on [interpolation](https://link.springer.com/chapter/10.1007/978-3-540-31980-1_1).
However, there is usually no single best variant: different algorithms are suitable for different verification tasks.
Therefore, generic frameworks are also emerging, which provide configurability, combinations of different strategies for abstraction and refinement, and support for various kind of models."

Quoted from [Á. Hajdu and Z. Micskei - Efficient Strategies for CEGAR-Based Model Checking, JAR 2020](https://link.springer.com/article/10.1007/s10817-019-09535-x)

## Options

Note that not all options might be available in all tools.
The available options are presented in the help screen of each tool.

### `--domain`

The domain controls the abstract information that is being tracked about the system.

* `PRED_CART`: [Cartesian predicate abstraction](https://link.springer.com/article/10.1007/s10009-002-0095-0) keeps track of conjunctions of logical predicates (e.g., `x > 5 and y = x`) instead of concrete values.
* `PRED_BOOL`: [Boolean predicate abstraction](https://link.springer.com/article/10.1007/s10009-002-0095-0) keeps track of arbitrary Boolean combination of predicates.
* `PRED_SPLIT`: Boolean predicate abstraction, but states are [split]((https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf)) into sub-states along disjunctions.
* `EXPL`: [Explicit-value abstraction]((https://link.springer.com/chapter/10.1007/978-3-642-37057-1_11)) keeps track of concrete values, but only for a (continuously expanded) set of variables.
* `PROD`: Product abstraction, available for XSTS models. The set of control variables (marked with `ctrl`) are tracked explicitly while others are tracked by predicates.

Predicate abstraction (`PRED_*`) tracks logical formulas instead of concrete values of variables, which can be efficient for variables with large (or infinite) domain.
Explicit-values (`EXPL`) keep track of a subset of system variables, which can be efficient if variables are mostly deterministic or have a small domain.
Cartesian predicate abstraction only uses conjunctions (more efficient) while Boolean allows arbitrary formulas (more expressive).
Boolean predicate abstraction often gives predicates in a disjunctive normal form (DNF).
In `PRED_BOOL` this DNF formula is treated as a single state, while in `PRED_SPLIT` each operand of the disjunction is a separate state.

It is recommended to try Cartesian first and fall back to Boolean if there is no refinement progress (seemingly infinite iterations with the same counterexample).
Splitting rarely results in better performance.

More information on the abstract domains can be found in Section 2.2.1 and 3.1.3 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf).

### `--initprec`

Controls the initial precision of the abstraction (e.g., what predicates or variables are tracked initially).

* `EMPTY`: Start with an empty initial precision.
* `ALLVARS`: Tracks all variables from the beginning. Available for CFA if `--domain` is `EXPL`.
* `ALLASSUMES`: Track all assumptions by default (e.g., branch/loop conditions). Only applicable for CFA and if `--domain` is `PRED_*`.
* `PROP`: Available for XSTS. Tracks variables from the property if `--domain` is `EXPL` and predicates from the property if `--domain` is `PRED_*`.
* `CTRL`: Available for XSTS if `--domain` is `PROD` or `EXPL`. Tracks all control variables.

We observed that usually the `EMPTY` initial precision yields good performance: the algorithm can automatically determine the precision.
However, if the system is mostly deterministic, it might be suitable to track all variables from the beginning.

### `--search`

Search strategy in the abstract state space. Determines the order in which abstract states are being processed.

* `BFS`: Standard breadth-first search.
* `DFS`: Standard depth-first search.
* `ERR`: Guide the search based on the syntactical distance from the error location (see Section 3.1.2 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information). Available for CFA.

We observed that`BFS` and `ERR` gives a good performance.

### `--encoding`

Available for CFA, determines the [points where abstraction is applied](https://ieeexplore.ieee.org/document/5351147) (granularity).

* `SBE`: Single-block encoding, where abstraction is performed at each edge (each statement).
* `LBE`: Large-block encoding, where sequential edges (statements) are treated as a single step for abstraction.

`SBE` is just a reference implementation, `LBE` is always more efficient.

### `--maxenum`

Available for CFA and XSTS.
Maximal number of states to be enumerated when performing explicit-value analysis (`--domain EXPL`) and an expression cannot be deterministically evaluated.
If the limit is exceeded, unknown values are propagated.
As a special case, `0` stands for infinite, but it should only be used if the model does not have any variable with unbounded domain (or that variable is deterministically assigned).
In general, values between `5` to `50` perform well (see Section 3.1.1 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information).

### `--refinement`

Strategy for refining the precision of the abstraction, i.e., inferring new predicates or variables to be tracked.

* `FW_BIN_ITP`: Forward binary interpolation. Searches for the first state where the counterexample becomes infeasible starting from the initial state. Only performs well if `--prunestrategy` is `FULL`.
* `BW_BIN_ITP`: Backward binary interpolation (see Section 3.2.1 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information). Searches backwards for the first state where the counterexample becomes infeasible starting from the target state.
* `SEQ_ITP`: Sequence interpolation.
* `MULTI_SEQ`: Sequence interpolation with multiple counterexamples (see Section 3.2.2 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information). Can be useful for models with high cyclomatic complexity to converge faster.
* `UNSAT_CORE`: Extract variables to be tracked from an unsat core, only available if `--domain` is `EXPL`.
* `UCB`: Extracts predicates or variables using weakest preconditions and unsat cores ([see paper](https://link.springer.com/chapter/10.1007%2F978-3-319-26287-1_10) for more information). _Experimental feature._ Available for CFA.
* `NWT_*`: Newton-style refinement. _Experimental feature._ Available for CFA. The following variants are supported ([see paper](https://dl.acm.org/doi/10.1145/3106237.3106307) for more information):
	* `NWT_SP` and `NWT_WP` only works for really simple inputs,
	* `NWT_SP_LV`, `NWT_WP_LV`, `NWT_IT_SP`, `NWT_IT_WP_LV`, `NWT_IT_SP_LV` has mixed performance,
	* `NWT_IT_WP` is usually the most effective.

`BW_BIN_ITP` and `SEQ_ITP` has the best performance usually. However, they usually do not work if bitvector types are involved (due to the limitation of the underlying SMT solver). For bitvectors, `NWT_IT_WP` is recommended.

### `--predsplit`

Available if `--domain` is `PRED_*`.
Determines whether splitting is applied to new predicates that are obtained during refinement.
* `WHOLE`: Keep predicates as a whole, no splitting is applied. Can perform well if the model has many Boolean variables.
* `CONJUNCTS`: Split predicates into conjuncts.
* `ATOMS`: Split predicates into atoms.

See Section 3.1.3 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information.

### `--precgranularity`

Granularity of the precision. Available for CFA.
* `GLOBAL`: The same precision is applied in each location of the CFA.
* `LOCAL`: Each location can have a possibly different precision.

### `--prunestrategy`

The pruning strategy controls which portion of the abstract state space is discarded during refinement.
* `FULL`: The whole abstract reachability graph (ARG) is pruned and abstraction is completely restarted with the new precision.
* `LAZY`: The ARG is only pruned back to the first point where refinement was applied. (See [Lazy abstraction](https://dl.acm.org/doi/10.1145/565816.503279).)

It is recommended to first try `LAZY` and fall back to `FULL` if there is no refinement progress (seemingly infinite iterations with the same counterexample).