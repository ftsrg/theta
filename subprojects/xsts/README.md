## Overview

This project contains the Extended Symbolic Transition System (XSTS) formalism. The project includes:

* Classes to represent STSs.
* A domain specific language (DSL) to parse XSTSs from a textual representation.

### Related projects

* [`xsts-analysis`](../xsts-analysis/README.md): XSTS specific analysis modules enabling the algorithms to operate on them.
* [`xsts-cli`](../xsts-cli/README.md): An executable tool (command line) for running analyses on XSTSs.

## XSTS Formalism

STSs consist of

* Variables,
* an initial expression describing the initial states,
* a set of atomic transitions
* a set of atomic environmental actions
* a property expression.

Algorithms are usually interested in proving that the property holds for every reachable state (safety property).

### Textual Representation (DSL)

An example XSTS realizing a counter:

```
var x: integer

trans {
    assume x<5;
    x:=x+1;
} or {
    x:=x;
}

init {
    x=0
}

env {}
```
