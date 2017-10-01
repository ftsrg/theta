## Overview

This project contains the Control Flow Automata (CFA) formalism. Its main purpose is to describe programs as a graphs, where edges are annotated with program statements. The project contains:

* Classes to represent CFAs.
* A domain specific language (DSL) to parse CFAs from a textual representation.
* CFA specific analysis modules enabling the algorithms to operate on them.
* An executable tool for running analyses on CFAs.

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

An unstable, prototype tool is available that can parse simple C programs into CFAs using Eclipse CDT. The tool can be downloaded [here](home.mit.bme.hu/~hajdua/theta/c-to-cfa.jar). This tool is no longer maintained as we are currently developing an LLVM frontend for CFAs.

## Tool

The tool can be built using the command `./gradlew theta-cfa` (Linux) or `gradle.bat theta-cfa` (Windows). The runnable file will appear under _build/libs_. The tool also requires the libraries in the _../lib_ folder (if you work on Windows, also read the README there).

The tool can be run with `java -jar theta-cfa.jar [arguments]`. If no arguments are given, a help screen is displayed about the arguments and their possible values. For example, put the example above in a file called `counter.cfa` and call `java -jar theta-cfa.jar -m counter.cfa -d EXPL -r SEQ_ITP -ll 3`.