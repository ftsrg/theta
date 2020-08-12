## Overview

This project contains an executable tool (command line) for running analyses on XTAs.

### Related projects

* [`xta`](../xta/README.md): Classes to represent XTAs and a domain specific language (DSL) to parse XTAs from a textual representation.
* [`xta-analysis`](../xta-analysis/README.md): XTA specific analysis modules enabling the algorithms to operate on them.

## Using the tool

1. First, get the tool.
    - The easiest way is to download a [pre-built release](https://github.com/ftsrg/theta/releases).
    - You can also [build](../../doc/Build.md) the tool yourself. The runnable jar file will appear under _build/libs/_ with the name _theta-xta-cli-\<VERSION\>-all.jar_, you can simply rename it to _theta-xta-cli.jar_.
    - Alternatively, you can use our docker image (see below).
2. Running the tool requires Java (JRE) 11.
3. The tool also requires the [Z3 SMT solver libraries](../../doc/Build.md) to be available on `PATH`.
4. The tool can be executed with `java -jar theta-xta-cli.jar [ARGUMENTS]`.
    - If no arguments are given, a help screen is displayed about the arguments and their possible values.
    More information can also be found below.

### Docker

A Dockerfile is also available under the _docker_ directory in the root of the repository.
The image can be built using the following command (from the root of the repository):
```
docker build -t theta-xta-cli -f docker/theta-xta-cli.Dockerfile .
```

The script `run-theta-xta-cli.sh` can be used for running the containerized version on models residing on the host:
```
./docker/run-theta-xta-cli.sh model.xta [OTHER ARGUMENTS]
```
Note that the model must be given as the first positional argument (without `--model`).
