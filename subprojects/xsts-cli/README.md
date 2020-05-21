## Overview

This project contains an executable tool (command line) for running analyses on XSTSs.

### Related projects

* [`xsts`](../xsts/README.md): Classes to represent XSTSs and a domain specific language (DSL) to parse XSTSs from a textual representation.
* [`xsts-analysis`](../xsts-analysis/README.md): XSTS specific analysis modules enabling the algorithms to operate on them.

## Tool

First, [build](../../doc/Build.md) the projects.
The runnable jar file will appear under _build/libs/_ with the name _theta-xsts-cli-\<VERSION\>-all.jar_.
You can simply rename it to _theta-xsts-cli.jar_.
The tool also requires the [Z3 SMT solver](../../doc/Build.md).

The tool can be run with `java -jar theta-xsts-cli.jar [arguments]`.
If no arguments are given, a help screen is displayed about the arguments and their possible values.
For example `java -jar theta-xsts-cli.jar --model trafficlight.xsts --property red_green.prop` runs the default analysis with the `red_green.prop` property on the `trafficlight.xsts` input file.