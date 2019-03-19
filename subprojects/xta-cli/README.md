## Overview

This project contains an executable tool (command line) for running analyses on XTAs.

### Related projects

* [`xta`](../xta/README.md): Classes to represent XTAs and a domain specific language (DSL) to parse XTAs from a textual representation.
* [`xta-analysis`](../xta-analysis/README.md): XTA specific analysis modules enabling the algorithms to operate on them.

## Tool

First, [build](../../doc/Build.md) the projects.
The runnable jar file will appear under _build/libs/_ with the name _theta-xta-cli-\<VERSION\>-all.jar_.
You can simply rename it to _theta-xta-cli.jar_.
The tool also requires the [Z3 SMT solver](../../doc/Build.md).

The tool can be run with `java -jar theta-xta-cli.jar [arguments]`.
If no arguments are given, a help screen is displayed about the arguments and their possible values.