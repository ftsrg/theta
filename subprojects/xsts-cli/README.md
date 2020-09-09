## Overview

The `xsts-cli` project is an executable (command line) tool for running CEGAR-based analyses on XSTSs.
For more information about the XSTS formalism and its supported language elements, take a look at the [`xsts`](../xsts/README.md) project.

### Related projects

* [`xsts`](../xsts/README.md): Classes to represent XSTSs and a domain specific language (DSL) to parse XSTSs from a textual representation.
* [`xsts-analysis`](../xsts-analysis/README.md): XSTS specific analysis modules enabling the algorithms to operate on them.

### Frontends
* [Gamma](https://github.com/ftsrg/gamma) is a statechart composition framework, that supports theta-xsts-cli as a backend to verify collaborating state machines.

## Using the tool

1. First, get the tool.
    * The easiest way is to download a [pre-built release](https://github.com/ftsrg/theta/releases).
    * You can also [build](../../doc/Build.md) the tool yourself. The runnable jar file will appear under _build/libs/_ with the name _theta-xsts-cli-\<VERSION\>-all.jar_, you can simply rename it to _theta-xsts-cli.jar_.
    * Alternatively, you can use our docker image (see below).
2. Running the tool requires Java (JRE) 11.
3. The tool also requires the [Z3 SMT solver libraries](../../doc/Build.md) to be available on `PATH`.
4. The tool can be executed with `java -jar theta-xsts-cli.jar [ARGUMENTS]`.
    * If no arguments are given, a help screen is displayed about the arguments and their possible values.
    More information can also be found below.
    * For example `java -jar theta-xsts-cli.jar --model crossroad.xsts --property "x>1" --loglevel INFO` runs the default analysis with logging on the `crossroad.xsts` model file with the property `x>1`.

### Docker

A Dockerfile is also available under the _docker_ directory in the root of the repository.
The image can be built using the following command (from the root of the repository):
```
docker build -t theta-xsts-cli -f docker/theta-xsts-cli.Dockerfile .
```

The script `run-theta-xsts-cli.sh` can be used for running the containerized version on models residing on the host:
```
./docker/run-theta-xsts-cli.sh crossroad.xsts --property "x>1" [OTHER ARGUMENTS]
```
Note that the model must be given as the first positional argument (without `--model`).

## Arguments

All arguments are optional, except `--model` and `--property`.

* `--model`: Path of the input XSTS model (mandatory).
* `--property`: Input property as a string or a file (*.prop) (mandatory).
* `--cex`: Output file where the counterexample is written (if the result is unsafe). If the argument is not given (default) the counterexample is not printed. Use `CON` (Windows) or `/dev/stdout` (Linux) as argument to print to the standard output.
* `--loglevel`: Detailedness of logging.
    * Possible values (from the least to the most detailed): `RESULT`, `MAINSTEP`, `SUBSTEP` (default), `INFO`, `DETAIL`, `VERBOSE`.
* `--domain`: Domain of the abstraction, possible values:
    * `PRED_CART`: Cartesian predicate abstraction (default).
    * `PRED_BOOL`: Boolean predicate abstraction.
    * `PRED_SPLIT`: Boolean predicate abstraction with splitting.
    * `EXPL`: Explicit-value abstraction.
    * `PROD`: Product abstraction with explicit-value and predicate abstraction.
    * _Remark: Predicate abstraction tracks logical formulas instead of concrete values of variables, which can be efficient for variables with large (or infinite) domain.
  Explicit-values keep track of a subset of system variables, which can be efficient if variables are mostly deterministic or have a small domain.
  Cartesian predicate abstraction only uses conjunctions (more efficient) while Boolean allows arbitrary formulas (more expressive).
  Boolean predicate abstraction often gives predicates in a disjunctive normal form (DNF).
  In `PRED_BOOL` this DNF formula is treated as a single state, while in `PRED_SPLIT` each operand of the disjunction is a separate state._
    * _Remark: It is recommended to try Cartesian first and fall back to Boolean if there is no refinement progress (seemingly infinite iterations with the same counterexample).
  Splitting rarely resulted in better performance._
    * _Remark: In `PROD` the set of control variables is handled explicitly, while other variables are covered by predicate abstraction. A variable can be added to the set of control variables by adding the keyword `ctrl` to its declaration. Example: `ctrl var x : integer` declares an integer control variable._
    * _More information on the abstract domains can be found in [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf), Sections 2.2.1 and 3.1.3._
* `--initprec`: Initial precision of the abstraction.
    * `EMPTY`: Start with an empty initial precision (default).
    * `PROP`: Track all variables of the property by default if `--domain` is `EXPL`. Construct predicates from the property if `--domain` is `PRED_*`.
    * `CTRL`: Track all control variables by default. Only applicable if `--domain` is `PROD` or `EXPL`.
* `--search`: Search strategy in the abstract state space, possible values:
    * `BFS` (default), `DFS`: Standard breadth- and depth-first search.
* `--maxenum`: Maximal number of states to be enumerated when performing explicit-value analysis (`--domain EXPL`) and an expression cannot be deterministically evaluated.
If the limit is exceeded, unknown values are propagated.
As a special (and default) case, `0` stands for infinite, but it should only be used if the model does not have any variable with unbounded domain.
In general, values between `5` to `50` perform well (see Section 3.1.1 of [our JAR paper](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) for more information).
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
* `--prunestrategy`: Pruning strategy during refinement, possible values:
    * `FULL`: The whole ARG is pruned and abstraction is completely restarted with the new precision.
    * `LAZY`(default): The ARG is only pruned back to the first point where refinement was applied.

### For developer usage

| Flag | Description |
|--|--|
| `--stacktrace` | Print full stack trace for exceptions. |
| `--benchmark` | Benchmark mode, only print metrics in csv format. |
| `--header` | Print the header for the benchmark mode csv format. |
