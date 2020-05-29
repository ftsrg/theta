## Overview

This project contains the Extended Symbolic Transition System (XSTS) formalism. The project includes:

* Classes to represent STSs.
* A domain specific language (DSL) to parse XSTSs from a textual representation.

### Related projects

* [`xsts-analysis`](../xsts-analysis/README.md): XSTS specific analysis modules enabling the algorithms to operate on them.
* [`xsts-cli`](../xsts-cli/README.md): An executable tool (command line) for running analyses on XSTSs.

## XSTS Formalism

XSTSs consist of

* type declarations (optional)
* variables
* an initial formula describing the initial states
* a set of atomic inner transitions
* a set of atomic environmental transitions (optional)
* a set of atomic init transitions (optional)
* a property expression.

Algorithms are usually interested in proving that the property holds for every reachable state (safety property).

### Type declarations

Custom types can be declared the following way:

`type <name> : { <literal_1>, . . . , <literal_n> }`

Example:

`type Color : { RED, GREEN, BLUE }`

### Variable declarations

XSTS contains the following built-in types: `integer`, `boolean`. Previously declared custom types can also be used in variable declarations.
Variables can be declared the following way:

`var <name> : <type>`

Variables can have initial values assigned to them the following way:

`var <name> : <type> = <value> `

Examples:

```
var a : integer
var b : boolean = false
var c : Color = RED
```

Please note that all variable names matching the pattern `temp([0-9])+` are reserved for use by the model checker.

### Textual Representation (DSL)

An example XSTS realizing a counter:

```
var x: integer = 0

trans {
    assume x<5;
    x:=x+1;
} or {
    x:=x;
}

init {}

env {}
```

An example property stating that the value of x will always be greater than or equal to 0:

```
prop{
    x>=0
}
```
