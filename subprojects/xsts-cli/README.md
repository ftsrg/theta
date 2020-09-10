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

The arguments related to the algorithm are described in more detail (along with best practices) in [CEGAR-algorithms.md](../../doc/CEGAR-algorithms.md).

### For developer usage

| Flag | Description |
|--|--|
| `--stacktrace` | Print full stack trace for exceptions. |
| `--benchmark` | Benchmark mode, only print metrics in csv format. |
| `--header` | Print the header for the benchmark mode csv format. |
