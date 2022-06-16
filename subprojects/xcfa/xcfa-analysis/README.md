## Overview
This project contains analysis modules related to the eXtended Control Flow Automata (XCFA) formalism. Its main purpose is to enable the algorithms to operate over XCFA models.

The following analyses are available:

1. [Declarative](src/main/java/hu/bme/mit/theta/xcfa/analysis/impl/declarative): Handling multi-threaded programs using a declarative approach. See [this](https://tdk.bme.hu/VIK/DownloadPaper/Ellenpeldaalapu-absztrakcio-finomitas) paper for further information.
2. [Interleavings](src/main/java/hu/bme/mit/theta/xcfa/analysis/impl/interleavings): Handling multi-threaded programs using an interleavings-based approach, i.e., discovering all relevant overlapping executions of the program. See [this](https://tdk.bme.hu/VIK/DownloadPaper/Ellenpeldaalapu-absztrakcio-finomitas) paper for further information.
3. [Singlethread](src/main/java/hu/bme/mit/theta/xcfa/analysis/impl/singlethread): Only handling single-threaded programs encoded in the XCFA formalism. This is a reimplementation of the CFA analysis project [here](../../cfa/cfa-analysis/README.md).

### Related projects

* [`analysis`](../../common/analysis/README.md): Common analysis modules.
* [`xcfa`](../xcfa/README.md): Classes to represent XCFAs.
* [`xcfa-cli`](../xcfa-cli/README.md): An executable tool (command line) for running analyses on XCFAs.