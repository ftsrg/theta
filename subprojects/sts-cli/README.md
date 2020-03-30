## Overview

This project contains an executable tool (command line) for running analyses on STSs.

### Related projects

* [`sts`](../sts/README.md): Classes to represent STSs and a domain specific language (DSL) to parse STSs from a textual representation.
* [`sts-analysis`](../sts-analysis/README.md): STS specific analysis modules enabling the algorithms to operate on them.

## Tool

First, [build](../../doc/Build.md) the projects.
The runnable jar file will appear under _build/libs/_ with the name _theta-sts-cli-\<VERSION\>-all.jar_.
You can simply rename it to _theta-sts-cli.jar_.
The tool also requires the [Z3 SMT solver](../../doc/Build.md).

The tool can be run with `java -jar theta-sts-cli.jar [arguments]`.
If no arguments are given, a help screen is displayed about the arguments and their possible values.
For example `java -jar theta-sts-cli.jar --model counter.system --loglevel INFO` runs the default analysis with logging on the `counter.system` input file.