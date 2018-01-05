## Overview

This project contains the Control Flow Automata (CFA) formalism. Its main purpose is to describe programs as a graphs, where edges are annotated with program statements. The project contains:

* Classes to represent CFAs.
* A domain specific language (DSL) to parse CFAs from a textual representation.
* CFA specific analysis modules enabling the algorithms to operate on them.
* An executable tool (command line and GUI) for running analyses on CFAs.

## CFA Formalism

A CFA is a directed graph with

* variables,
* locations, with dedicated initial, final and error locations,
* edges between locations, labeled with statements over the variables.

Algorithms are usually interested in proving that the error location is not reachable.

### Textual representation (DSL)

An example CFA realizing a counter:

```
main process counter {
    var x : int

    init loc L0
    loc L1
    loc L2
    loc L3
    final loc END
    error loc ERR

    L0 -> L1 { x := 0 }
    L1 -> L2 { assume x < 5 }
    L1 -> L3 { assume not (x < 5) }
    L2 -> L1 { x := x + 1 }
    L3 -> END { assume x <= 5 }
    L3 -> ERR { assume not (x <= 5) }
}
```

See _src/test/resources_ for more examples.

### C source to CFA

An unstable, prototype tool is available that can parse simple C programs into CFAs using Eclipse CDT. The tool can be downloaded [here](http://home.mit.bme.hu/~hajdua/theta/c-to-cfa.jar). This tool is no longer maintained as we are currently developing an LLVM frontend for CFAs.

## Tool

Use one of the following commands to build the tool.

- Linux, command line: `./gradlew theta-cfa-cli`
- Linux, GUI: `./gradlew theta-cfa-gui`
- Windows, command line: `gradlew.bat theta-cfa-cli`
- Windows, GUI: `gradlew.bat theta-cfa-gui`

The runnable file will appear under _build/libs_. The tool also requires [Z3 and GraphViz](../doc/Dependencies.md).

The command line tool can be run with `java -jar theta-cfa-cli.jar [arguments]`. If no arguments are given, a help screen is displayed about the arguments and their possible values. For example, put the example above in a file called `counter.cfa` and call `java -jar theta-cfa-cli.jar --model counter.cfa --domain EXPL --refinement SEQ_ITP --loglevel INFO`.

The GUI tool can be run simply by executing `theta-cfa-gui.jar`. Use the controls to load the model, adjust parameters and run the algorithm.
