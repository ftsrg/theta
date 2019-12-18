## Overview

This project contains the eXtended Control Flow Automata (XCFA) formalism. Its main purpose is to describe programs as groups of graphs, where edges are annotated with program statements and each graph represents a single procedure in a single process. The project contains:

* Classes to represent XCFAs.
* A domain specific language (DSL) to parse XCFAs from a textual representation.

### Related projects

* [`cfa`](../cfa/README.md): The ancestor project of the XCFA formalism, it can represent single-process single-procedure programs.  
* [`xcfa-analysis`](../xcfa-analysis/README.md): XCFA specific analysis modules enabling the algorithms to operate on them.
* [`xcfa-cli`](../xcfa-cli/README.md): An executable tool (command line) for running analyses on XCFAs. Currently only CFA-like XCFAs are supported.

## XCFA formalism

An XCFA is a process- and procedure-based collection of directed graphs (`V`, `L`, `E`) with

* variables `V = {v1, v2, ..., vn}`,
* locations `L`, with dedicated initial (`l0`), final (`lf`) and error (`le`) locations,
* edges `E` between locations, labeled with statements over the variables.
Statements can be
  * assignments of the form `v := expr`, where `expr` is an expression with the same type as `v`,
  * assumptions of the form `assume expr`, where `expr` is a Boolean expression,
  * havocs of the form `havoc v`,
  * boundaries of atomic blocks `AtomicBegin`, `AtomicEnd`,
  * synchronization primitives `Wait`, `Notify`, `NotifyAll`,
  * memory operation primitives `Load`, `Store` with optional annotation of `atomic @ordering` where `ordering` is a memory ordering primitive,
  * call statements of the form `call proc` where `proc` is a referenced procedure (by name).

### Textual representation (DSL)

An example XCFA realizing a two-threaded counter:

```
var x : int
main process counter {
  main procedure procedure1() {
    var i : int
    init loc L0
    loc L1
    loc L2
    loc L3
    loc L4
    final loc END
    error loc ERR

    L0 -> L1 { i <- x atomic @relaxed }
    L1 -> L2 { assume i < 5 }
    L1 -> L4 { assume not (i < 5) }
    L2 -> L3 { i := i + 1 }
    L3 -> L1 { i -> x atomic @relaxed }
    L4 -> END { assume i <= 5 }
    L4 -> ERR { assume not (i <= 5) }
  }
}
```

See _src/test/resources_ for more examples and _src/main/antlr_ for the full grammar.