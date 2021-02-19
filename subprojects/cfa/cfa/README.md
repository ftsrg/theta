## Overview

This project contains the Control Flow Automata (CFA) formalism. Its main purpose is to describe programs as a graphs, where nodes correspond to program locations and edges are annotated with program statements.
The project contains:
* Classes to represent CFAs.
* A domain specific language (DSL) to parse CFAs from a textual representation.

### Related projects

* [`cfa-analysis`](../cfa-analysis/README.md): CFA specific analysis modules enabling the algorithms to operate on them.
* [`cfa-cli`](../cfa-cli/README.md): An executable (command line) tool for running analyses on CFAs.

## CFA formalism

A CFA is a directed graph (`V`, `L`, `E`) with

* variables `V = {v1, v2, ..., vn}`,
* locations `L`, with a dedicated initial (`l0`) location and optionally with dedicated final (`lf`) and error (`le`) locations,
* edges `E` between locations, labeled with statements over the variables.

Currently, there are three kind of supported statements.
* Assignments have the form `v := expr`, where `expr` is a side-effect free expression with the same type as `v`.
After performing the assignment statement, the value of variable `v` is the result of evaluating `expr`.
For example, if `x` is `1` and the assignment `x := x + 1` is performed, `x` becomes `2` (and the rest of the variables are unchanged).
* Assumptions have the form `assume expr`, where `expr` is a side-effect free Boolean expression.
It is only possible to take the edge if `expr` evaluates to true.
For example, `assume x == 0` can be taken if and only if `x` equals `0`.
After the assumption, variables are unchanged.
* Havocs have the form `havoc v`.
After performing the havoc, `v` is assigned a non-deterministic value.
This can be used to simulate non-deterministic input from the user or the environment.

Algorithms are usually interested in proving that the error location (given in the CFA or as a separate argument) is not reachable.
For more information see Section 2 of the [Software Verification Supplementary Material](https://ftsrg.mit.bme.hu/software-verification-notes/software-verification.pdf), which also includes examples on how to encode programs as CFA.

Variables of the CFA can have the following types.
* `bool`: Booleans.
* `int`: Mathematical, unbounded SMT integers.
* `rat`: Rational numbers (implemented as SMT reals).
* `[K] -> V`: SMT arrays (associative maps) from a given key type `K` to a value type `V`.
* `bv[L]`: Bitvector of given length `L`. _This is an experimental feature. See the [details](doc/bitvectors.md) for more information._

Expressions of the CFA include the following.
* Identifiers (variables).
* Literals, e.g., `true`, `false` (Bool), `0`, `123` (integer), `4 % 5` (rational).
  * Array literals can be given by listing the key-value pairs and the (mandatory) default element, e.g., `[0 <- 182, 1 <- 41, default <- 75]`. If there are no elements, the key type has to be given before the default element, e.g., `[<int>default <- 75]`.
  * Bitvector literals can be given by stating the length and the exact value of the bitvector in binary, decimal or hexadecimal form. (E.g. `4'd5` is a 4-bit-long bitvector with the decimal value 5.) _This is an experimental feature. See the [details](doc/bitvectors.md) for more information._
* Comparison, e.g., `=`, `/=`, `<`, `>`, `<=`, `>=`.
* Boolean operators, e.g., `and`, `or`, `xor`, `not`, `imply`, `iff`.
* Arithmetic, e.g., `+`, `-`, `/`, `*`, `mod`, `rem`.
* Conditional: `if . then . else .`.
* Array read (`a[i]`) and write (`a[i <- v]`).
* Bitvector specific operators, e.g., `bvand`, `bvor`, `bvxor`, `bvshl`, `bvashr`, `bvlshr`, `bvrol`, `bvror`, `bvnot`, etc. _This is an experimental feature. See the [details](doc/bitvectors.md) for more information._

### Textual representation (DSL)

As an example, consider a simple program (written in a C-like language) that counts up to 5 and asserts the result to be less than or equal to 5:
```c
int x = 0;
while (x < 5) {
  x++;
}
assert x <= 5;
```

The program above can be represented by the following CFA:
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
Note that for example the loop in the program appears as a cycle (`L1 -> L2 -> L1`) in the CFA.
The assertion is modeled with a branching in the CFA: if it holds, `L3 -> END` is taken, otherwise `L3 -> ERR`.

Variables can be defined by `var <NAME> : <TYPE>`, locations by `(init|final|error|) loc <NAME>`, and edges by `<SOURCE> -> <TARGET> {<STATEMENT>}`.
As a syntactic sugar, it is possible to include multiple statements on one edge (in new lines).
In this case, anonymus intermediate locations will automatically be introduced when parsing the CFA.
For example,
```
L0 -> L1 {
   x := 0
   assume x >= 0
}
```
introduces an intermediate location `""` (with an empty string as name) between `L0` and `L1`.
There will be an edge `x := 0` from `L0`to `""` and an edge `assume x >= 0` from `""` to `L1`.

See _src/test/resources_ for more examples and _src/main/antlr_ for the full grammar.

### Frontends

* [Gazer](https://github.com/ftsrg/gazer) is an [LLVM](https://llvm.org/)-based frontend to verify C programs using theta-cfa-cli, also giving support towards [SV-COMP](https://sv-comp.sosy-lab.org/2021/). See our [tool paper at TACAS](https://ftsrg.mit.bme.hu/theta/publications/tacas2021.pdf) for more information.
* [PLCverif](https://cern.ch/plcverif) is a tool developed at CERN for the formal specification and verification of PLC (Programmable Logic Controller) programs, supporting theta-cfa-cli as one of its verification backends.
