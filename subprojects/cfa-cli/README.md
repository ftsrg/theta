## Overview

This project contains an executable tool (command line) for running analyses on CFAs.

### Related projects

* [`cfa`](../cfa/README.md): Classes to represent CFAs and a domain specific language (DSL) to parse CFAs from a textual representation.
* [`cfa-analysis`](../cfa-analysis/README.md): CFA specific analysis modules enabling the algorithms to operate on them.

## Tool

First, [build](../../doc/Build.md) the projects.
The runnable jar file will appear under _build/libs/_ with the name _theta-cfa-cli-\<VERSION\>-all.jar_.
You can simply rename it to _theta-cfa-cli.jar_.
The tool also requires the [Z3 SMT solver](../../doc/Build.md).

The tool can be run with `java -jar theta-cfa-cli.jar [arguments]`.
If no arguments are given, a help screen is displayed about the arguments and their possible values.
For example, put the example above in a file called `counter.cfa` and call `java -jar theta-cfa-cli.jar --model counter.cfa --domain EXPL --refinement SEQ_ITP --loglevel INFO`.
