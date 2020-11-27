## Overview

The `cfa-cli` project is an executable (command line) tool for running CEGAR-based location-reachability analyses on CFAs.
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
* `--errorloc`: Name of the error (target) location in the CFA, which is checked for reachability. The CFA is safe if the error location is not reachable, and unsafe otherwise. This argument can be omitted if a location in the CFA is marked with the error keyword. If there is an error location marked in the CFA and this argument is also given, the argument has priority.
* `--cex`: Output file where the counterexample is written (if the result is unsafe). If the argument is not given (default) the counterexample is not printed. Use `CON` (Windows) or `/dev/stdout` (Linux) as argument to print to the standard output.
* `--loglevel`: Detailedness of logging.
    * Possible values (from the least to the most detailed): `RESULT`, `MAINSTEP`, `SUBSTEP` (default), `INFO`, `DETAIL`, `VERBOSE`.
* `--metrics`: Print metrics about the CFA without running the algorithm.
* `--visualize`: Visualize the CFA without running the algorithm.
If the extension of the output file is `pdf`, `png` or `svg` an automatic visualization is performed, for which [GraphViz](../../doc/Build.md) has to be available on `PATH`.
Otherwise, the output is simply in `dot` format.

The arguments related to the algorithm are described in more detail (along with best practices) in [CEGAR-algorithms.md](../../doc/CEGAR-algorithms.md).
* `--version`: Print version info (in this case `--model` is of course not required).

### For developer usage

| Flag | Description |
|--|--|
| `--stacktrace` | Print full stack trace for exceptions. |
| `--benchmark` | Benchmark mode, only print metrics in csv format. |
| `--header` | Print the header for the benchmark mode csv format. |
