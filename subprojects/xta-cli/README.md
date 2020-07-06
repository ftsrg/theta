## Overview

This project contains an executable tool (command line) for running analyses on XTAs.

### Related projects

* [`xta`](../xta/README.md): Classes to represent XTAs and a domain specific language (DSL) to parse XTAs from a textual representation.
* [`xta-analysis`](../xta-analysis/README.md): XTA specific analysis modules enabling the algorithms to operate on them.

## Tool

1. [Build](../../doc/Build.md) the projects.
The runnable jar file will appear under _build/libs/_ with the name _theta-xta-cli-\<VERSION\>-all.jar_.
2. You can simply rename it to _theta-xta-cli.jar_.
3. The tool also requires the [Z3 SMT solver](../../doc/Build.md) to be available on `PATH`.
4. The tool can be executed with `java -jar theta-xta-cli.jar [arguments]`.
    - If no arguments are given, a help screen is displayed about the arguments and their possible values.
    More information can also be found below.

### Docker (beta)

An experimental Dockerfile is also available under the _docker_ directory in the root of the repository.
The image can be built using the following command:
```
docker build -t theta-xta-cli -f theta-xta-cli.Dockerfile .
```

The script `run-theta-xta-cli.sh` can be used for running the containerized version on models residing on the host:
```
./run-theta-xta-cli.sh model.xta [OTHER FLAGS]
```
Note that the model must be given as the first positional argument (without `--model`).