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

`type <name> : { <literal>, . . . , <literal> }`

Example:

`type Color : { RED, GREEN, BLUE }`

### Variable declarations

The XSTS formalism contains the following built-in types: `integer`, `boolean`. Previously declared custom types can also be used in variable declarations.
Variables can be declared the following way:

`var <name> : <type>`

Variables can and in most cases should have initial values assigned to them, these values will be used to construct the formula that describes the initial states of the system. Assigning initial values is optional, but please note that for accurate model checking results all initial states described by the formula must be valid states of the system. Initial values can be assigned during variable declaration the following way: 

`var <name> : <type> = <value> `

Examples:

```
var a : integer
var b : boolean = false
var c : Color = RED
```

All variable names matching the pattern `temp([0-9])+` are reserved for use by the model checker.

### Transitions

The behaviour of XSTSs can be described using transitions. A transition is an atomic sequence of statements.
An XSTS contains 3 sets of transitions, each having different semantics.


#### Inner transitions

Inner transitions describe the behaviour of the system. The set of inner transitions can be declared the following way:

```
trans {
    <statement>
    ... 
    <statement>
} or {
    <statment>
    ...
    <statement>
}
```

Each branch is interpreted as a separate transition.

#### Environmental transitions

Environmental transitions are used to describe the system's interactions with its environment, for example incoming and outgoing events.

```
env {
    <statement>
    ... 
    <statement>
} or {
    <statment>
    ...
    <statement>
}
```

If you do not wish to use environmental transitions in your system, then leave the brackets empty: `env {}` This will result in a skip statement, which does nothing.

#### Init transitions



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
