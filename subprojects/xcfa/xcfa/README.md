## Overview

This project contains the eXtended Control Flow Automata (XCFA) formalism. Its main purpose is to describe programs as
groups of graphs, where edges are annotated with program statements and each graph represents a single procedure in a
single process. The project contains:

* Classes to represent XCFAs.
* A domain specific language (DSL) to parse XCFAs from a textual representation.
* A program transformation method that takes LLVM IR and creates an XCFA. 

Every _XCFA_ model consists of global variables and _XcfaProcess_ definitions. _XcfaProcesses_ consist of thread-local variables and _XcfaProcedure_ definitions. _XcfaProcedures_ are akin to the _CFA_ models, in the sense that they consist of local variables, _XcfaLocations_ and _XcfaEdges_; and _XcfaEdges_ contain zero or more statements.

Semantically, the _XCFA_ formalism describes an _asynchronous_ system, where processes are constantly executing statements on enabled transitions nondeterministically, until no such process remains (which either means a deadlock situation, or a completed execution). Statements are always atomic, but groups of statements can also be specified to be atomic when enclosed among _AtomicBeginStmt_ and _AtomicEndStmt_ statements. After any number of executed _AtomicBeginStmts_ a single _AtomicEndStmt_ ends the atomic block, and an _AtomicEndStmt_ is no-op without a preceding _AtomicBeginStmt_.

_XCFA_ models can be _static_ or _dynamic_ depending on whether all threads are spawned on entry, or threads can spawn and await other threads. 

### Related projects

* [`cfa`](../cfa/README.md): The ancestor project of the XCFA formalism, it can represent single-process
  single-procedure programs.
* [`xcfa-cli`](../xcfa-cli/README.md): An executable tool (command line) for running analyses on XCFAs. Currently only
  CFA-like XCFAs are supported.
* [`xcfa-analysis`](../xcfa-analysis/README.md): The analyses that work on XCFAs: a BMC-like and a CEGAR based algorithm.
* [`cat`](../cat/README.md): The memory modeling language that is used by the analyses above.

## XCFA C-Frontend

This subproject adds an ANTLR-grammar based C-Frontend to Theta. This is independent of any formalism, and aims to be as widely applicable as possible.

### Features

This frontend can handle preprocessed .c or .i file with the following features:

* Basic C support: global declarations (functions and variables), function definitions, loops, various data types, global typedefs, etc.
* Integer- and bitvector-arithmetic support based on required features (e.g. for floats or bitwise operators bitvector precision is necessary)
* Basic struct and array support
* Basic (and experimental) flat-memory based pointer handling
* ILP32 and LP64 type system support (with possible extensibility)

### Limitations, known bugs

A number of features are either not well tested or in certain aspects buggy. Error handling is done on a best-effort level as the C specification is way too complex to handle entirely correctly. In most cases an error, or a warning message is displayed, but in some unexpected situations a silent failure is also possible.

In particular, the following features are either not implemented or can produce buggy models:

* Floating-point pointers (produces an exception when (de)referred)
* Structs including arrays and arrays including structs (produces an exception when accessed)
* Enums (only produces a warning, behaves as a normal signed int would)
* Unions (produces an exception when any element is accessed) 
* Alignof, Sizeof, various extensions (produces a parsing exception)
* Pointer arithmetic (produces an exception)
* Using a non-specific subtype of `char` (produces a warning) - use `(un)signed char` instead
* Includes and other preprocessor directives (produces an exception or fails silently!)
* Arrays are not pointers and pointers cannot be used as arrays (produces an exception)
* Memory access is _not_ checked, and therefore it is easy to receive a faulty value by over-indexing an array (fails silently!)
* Array elements are not range-checked and therefore false positives are possible (consider `char c[2]; if(c[1] > 500) reach_error()`)

Note that only program elements that are (transitively) reachable from main() are checked against any violation of the above criteria, i.e. a program containing unsupported elements that are not utilized is handled correctly. This is necessary for handling most preprocessed (.i) files, as the standard library includes a lot of complex and unsupported code. 

## XCFA formalism

An XCFA is a process- and procedure-based collection of directed graphs (`V`, `L`, `E`) with

* variables `V = {v1, v2, ..., vn}`,
* locations `L`, with dedicated initial (`l0`), final (`lf`) and error (`le`) locations,
* edges `E` between locations, labeled with statements over the variables. Statements can be
    * assignments of the form `v := expr`, where `expr` is an expression with the same type as `v`,
    * assumptions of the form `assume expr`, where `expr` is a Boolean expression,
    * havocs of the form `havoc v`,
    * boundaries of atomic blocks `AtomicBegin`, `AtomicEnd`,
    * memory operation primitives `Load`, `Store` with optional annotation of `atomic @ordering` where `ordering` is a
      memory ordering primitive,
    * call statements of the form `call proc` where `proc` is a referenced procedure (by name).

### Textual representation (DSL)

An example XCFA realizing a two-threaded counter:

```
var x : int
main process counter1 {
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
main process counter2 {
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
