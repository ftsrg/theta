## Overview

The `cfa-cli` project is an executable (command line) tool for running CEGAR-based analyses on CFAs.
Furthermore, it also includes some utilities, such as calculating metrics or visualizing the CFA.
For more information about the CFA formalism and its supported language elements, take a look at the [`cfa`](../cfa/README.md) project.

### Related projects

* [`cfa`](../cfa/README.md): Classes to represent CFAs and a domain specific language (DSL) to parse CFAs from a textual representation.
* [`cfa-analysis`](../cfa-analysis/README.md): CFA specific analysis modules enabling the algorithms to operate on them.

### Frontends

* [Gazer](https://github.com/FTSRG/gazer) is an [LLVM](https://llvm.org/)-based frontend to verify C programs using theta-cfa-cli as a backend.
* [PLCverif](https://cern.ch/plcverif) is a tool developed at CERN for the formal specification and verification of PLC (Programmable Logic Controller) programs, supporting theta-cfa-cli as one of its verification backends.

## Using the tool

1. First, get the tool.
    * The easiest way is to download a [pre-built release](https://github.com/ftsrg/theta/releases).
    * You can also [build](../../doc/Build.md) the tool yourself. The runnable jar file will appear under _build/libs/_ with the name _theta-cfa-cli-\<VERSION\>-all.jar_, you can simply rename it to _theta-cfa-cli.jar_.
    * Alternatively, you can use our docker image (see below).
2. Running the tool requires Java (JRE) 11.
3. The tool also requires the [Z3 SMT solver libraries](../../doc/Build.md) to be available on `PATH`.
4. The tool can be executed with `java -jar theta-cfa-cli.jar [ARGUMENTS]`.
    * If no arguments are given, a help screen is displayed about the arguments and their possible values.
    More information can also be found below.
    * For example `java -jar theta-cfa-cli.jar --model counter.cfa --loglevel INFO` runs the default analysis with logging on the `counter.cfa` input file.

### Docker

A Dockerfile is also available under the _docker_ directory in the root of the repository.
The image can be built using the following command (from the root of the repository):
```
docker build -t theta-cfa-cli -f docker/theta-cfa-cli.Dockerfile .
```

The script `run-theta-cfa-cli.sh` can be used for running the containerized version on models residing on the host:
```
./docker/run-theta-cfa-cli.sh model.cfa [OTHER ARGUMENTS]
```
Note that the model must be given as the first positional argument (without `--model`).

## Arguments

All arguments are optional, except `--model`.

* `--model`: Path of the input CFA model (mandatory).
* `--cex`: Output file where the counterexample is written (if the result is unsafe). If the argument is not given (default) the counterexample is not printed. Use `CON` (Windows) or `/dev/stdout` (Linux) as argument to print to the standard output.
* `--loglevel`: Detailedness of logging.
    * Possible values (from the least to the most detailed): `RESULT`, `MAINSTEP`, `SUBSTEP` (default), `INFO`, `DETAIL`, `VERBOSE`.
* `--domain`: Domain of the abstraction, possible values:
    * `PRED_CART`: Cartesian predicate abstraction (default).
    * `PRED_BOOL`: Boolean predicate abstraction.
    * `PRED_SPLIT`: Boolean predicate abstraction with splitting.
    * `EXPL`: Explicit-value abstraction.
    * _Remark: Predicate abstraction tracks logical formulas instead of concrete values of variables, which can be efficient for variables with large (or infinite) domain.
  Explicit-values keep track of a subset of system variables, which can be efficient if variables are mostly deterministic or have a small domain.
  Cartesian predicate abstraction only uses conjunctions (more efficient) while Boolean allows arbitrary formulas (more expressive).
  Boolean predicate abstraction often gives predicates in a disjunctive normal form (DNF).
  In `PRED_BOOL` this DNF formula is treated as a single state, while in `PRED_SPLIT` each operand of the disjunction is a separate state._
    * _Remark: It is recommended to try Cartesian first and fall back to Boolean if there is no refinement progress (seemingly infinite iterations with the same counterexample).
  Splitting rarely resulted in better performance._
    * _More information on the abstract domains can be found in [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf), Sections 2.2.1 and 3.1.3._
* `--initprec`: Initial precision of the abstraction.
    * `EMPTY`: Start with an empty initial precision (default).
    * `ALLVARS`: Track all variables by default (only applicable if `--domain` is `EXPL`).
    * `ALLASSUMES`: Track all assumptions by default (e.g., branch/loop conditions). Only applicable if `--domain` is `PRED_*`.
* `--search`: Search strategy in the abstract state space, possible values:
    * `BFS` (default), `DFS`: Standard breadth- and depth-first search.
    * `ERR`: Guide the search based on the syntactical distance from the error location (see Section 3.1.2 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information).
* `--encoding`: Encoding of the CFA during abstraction, possible values:
    * `SBE`: Single-block encoding, where abstraction is performed at each edge.
  This is just a reference implementation, `LBE` is always more efficient.
    * `LBE` (default): Large-block encoding, where sequential paths are treated as a single step for abstraction.
* `--maxenum`: Maximal number of states to be enumerated when performing explicit-value analysis (`--domain EXPL`) and an expression cannot be deterministically evaluated.
If the limit is exceeded, unknown values are propagated.
As a special case, `0` stands for infinite, but it should only be used if the model does not have any variable with unbounded domain.
In general, values between `5` to `50` perform well (see Section 3.1.1 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information). The default is `10`.
* `--refinement`: Refinement strategy, possible values:
    * `FW_BIN_ITP`: Forward binary interpolation, only performs well if `--prunestrategy` is `FULL`.
    * `BW_BIN_ITP`: Backward binary interpolation (see Section 3.2.1 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information).
    * `SEQ_ITP` (default): Sequence interpolation.
    * `MULTI_SEQ`: Sequence interpolation with multiple counterexamples (see Section 3.2.2 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information).
    * `UNSAT_CORE`: Unsat cores, only available if `--domain` is `EXPL`.
    * _Remark: `BW_BIN_ITP` and `SEQ_ITP` has the best performance usually._
* `--predsplit`: Splitting applied to predicates during refinement, possible values:
    * `WHOLE` (default): Keep predicates as a whole, no splitting is applied. Can perform well if the model has many Boolean variables.
    * `CONJUNCTS`: Split predicates into conjuncts.
    * `ATOMS`: Split predicates into atoms.
* `--precgranularity`: Granularity of the precision, possible values:
    * `GLOBAL` (default): The same precision is applied in each location of the CFA.
    * `LOCAL`: Each location can have a possibly different precision.
* `--prunestrategy`: Pruning strategy during refinement, possible values:
    * `FULL`: The whole ARG is pruned and abstraction is completely restarted with the new precision.
    * `LAZY`(default): The ARG is only pruned back to the first point where refinement was applied.
* `--metrics`: Print metrics about the CFA without running the algorithm.
* `--visualize`: Visualize the CFA without running the algorithm.
If the extension of the output file is `pdf`, `png` or `svg` an automatic visualization is performed, for which [GraphViz](../../doc/Build.md) has to be available on `PATH`.
Otherwise, the output is simply in `dot` format.

### For developer usage

| Flag | Description |
|--|--|
| `--stacktrace` | Print full stack trace for exceptions. |
| `--benchmark` | Benchmark mode, only print metrics in csv format. |
| `--header` | Print the header for the benchmark mode csv format. |
