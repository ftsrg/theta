## Overview

Note that a textual representation is currently not in development. Use
the [XCFA Builder](src/main/java/hu/bme/mit/theta/xcfa/model/XCFA.java) API for constructing XCFAs.

This project contains the eXtended Control Flow Automata (XCFA) formalism. Its main purpose is to
describe programs as
groups of graphs, where edges are annotated with program statements and each graph represents a
single procedure in a
single process. The project contains:

* Classes to represent XCFAs.
* A domain specific language (DSL) to parse XCFAs from a textual representation.
* A program transformation method that takes LLVM IR and creates an XCFA.

Every _XCFA_ model consists of global variables and _XcfaProcess_ definitions. _XcfaProcesses_
consist of thread-local variables and _XcfaProcedure_ definitions. _XcfaProcedures_ are akin to the
_CFA_ models, in the sense that they consist of local variables, _XcfaLocations_ and _XcfaEdges_;
and _XcfaEdges_ contain zero or more _XcfaLabels_.

Semantically, the _XCFA_ formalism describes an _asynchronous_ system, where processes are
constantly executing statements on enabled transitions nondeterministically, until no such process
remains (which either means a deadlock situation, or a completed execution). Statements are always
atomic, but groups of statements can also be specified to be atomic when enclosed among
_AtomicBeginStmt_ and _AtomicEndStmt_ statements. After any number of executed _AtomicBeginStmts_ a
single _AtomicEndStmt_ ends the atomic block, and an _AtomicEndStmt_ is no-op without a preceding
_AtomicBeginStmt_.

_XCFA_ models can be _static_ or _dynamic_ depending on whether all threads are spawned on entry, or
threads can spawn and await other threads.

### _XcfaLabels_

_XcfaLabels_ are used in place of the CFA-like statements. The change was warranted by the excessive
use of meta-statements
(i.e., statements that do not modify the actual data state but rather contain metainformation on the
program flow).

The following labels are used:

* `AtomicBeginXcfaLabel`: signals the beginning of an atomic (uninterruptible) block
* `AtomicEndXcfaLabel`: signals the end of an atomic block
* `ProcedureCallXcfaLabel `: invokes a procedure with a set of in/out/inout parameter expressions.
* `StartThreadXcfaLabel`: spawns a new process from an _XcfaProcess_ template with a set of
  parameter expressions
* `JoinThreadXcfaLabel`: join a running process based on its unique PID (i.e., await its
  termination)
* `LoadXcfaLabel`: Loads a global variable into a local variable. Semantics are tie to the governing
  memory model. An additional label (ordering) can be given to the label, which can be referenced by
  the memory models.
* `StoreXcfaLabel`: Stores a local variable into a global variable. The same notes apply to this
  label as to the `LoadXcfaLabel`.
* `FenceXcfaLabel`: Signals a synchronization among global memory operations. The same notes apply
  to this label as to the `LoadXcfaLabel`.
* `SequenceLabel`: Grouping a sequence of labels into a single unit. See `SequenceStmt` for its
  motivation.
* `NondetLabel`: Grouping nondeterministic alternatives together. See `NondetStmt` for its
  motivation. Support for this lable is experimental.
* `StmtXcfaLabel`: Contains a single `Stmt`.

### Related projects

* [`cfa`](../../cfa/cfa/README.md): The ancestor project of the XCFA formalism, it can represent
  single-process
  single-procedure programs.
* [`xcfa-cli`](../xcfa-cli/README.md): An executable tool (command line) for running analyses on
  XCFAs.
* [`xcfa-analysis`](../xcfa-analysis/README.md): The analyses that work on XCFAs.
* [`cat`](../cat/README.md): The memory modeling language that is used by the analyses above.
* [`c-frontend`](../../frontends/c-frontend/README.md): The c-frontend