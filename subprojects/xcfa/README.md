## Overview

This project contains the Control Flow Automata (XCFA) formalism. Its main purpose is to describe programs as a graphs, where edges are annotated with program statements. The project contains:

* Classes to represent XCFAs.
* A domain specific language (DSL) to parse XCFAs from a textual representation.

### Related projects

* [`xcfa-analysis`](../xcfa-analysis/README.md): XCFA specific analysis modules enabling the algorithms to operate on them.
* [`xcfa-cli`](../xcfa-cli/README.md): An executable tool (command line) for running analyses on XCFAs.

## XCFA formalism

A XCFA is a directed graph (`V`, `L`, `E`) with

* variables `V = {v1, v2, ..., vn}`,
* locations `L`, with dedicated initial (`l0`), final (`lf`) and error (`le`) locations,
* edges `E` between locations, labeled with statements over the variables.
Statements can be
  * assignments of the form `v := expr`, where `expr` is an expression with the same type as `v`,
  * assumptions of the form `assume expr`, where `expr` is a Boolean expression,
  * havocs of the form `havoc v`.

Algorithms are usually interested in proving that the error location is not reachable.

### Textual representation (DSL)

An example XCFA realizing a counter:

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

See _src/test/resources_ for more examples and _src/main/antlr_ for the full grammar.

### C source to XCFA

An unstable, prototype tool is available that can parse simple C programs into XCFAs using Eclipse CDT.
The tool can be downloaded [here](http://home.mit.bme.hu/~hajdua/theta/c-to-xcfa.jar). 
his tool is no longer maintained as we are currently developing an LLVM frontend for XCFAs.