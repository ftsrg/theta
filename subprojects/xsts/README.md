## Overview

This project contains the Extended Symbolic Transition System (XSTS) formalism. The project includes:

* Classes to represent XSTSs.
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

When using product abstraction (`PROD`), variables tagged as control variables are tracked explicitly. A variable can be tagged as a control variable with the keyword `ctrl`:

`ctrl var <name> : <type>`

Examples:

```
var a : integer
var b : boolean = false
var c : Color = RED
ctrl var x : integer = 0
```

All variable names matching the pattern `temp([0-9])+` are reserved for use by the model checker.

### Transitions

The behaviour of XSTSs can be described using transitions. A transition is an atomic sequence of statements. Statements can be:
* atomic statements (atomic statements always end with semicolons):
    * assignments of the form `<varname> := <expr>`, where `<varname>` is the name of a variable and `<expr>` is an expression of the same type
    * assumptions of the form `assume <expr>`, where `<expr>` is a boolean expression
    * havocs of the form `havoc <varname>`
* composite statements:
    * nondeterministic choices of the form `choice { <statement> } or { <statement> }`, with 1 or more branches
    * sequences of the form `<statement> <statement> <statement>`
    
Only those branches of a choice statement are considered for execution, of which all contained assumptions evaluate to true.

Example:

```
x := 1;
choice {
    assume y<2;
    x := x+y;
} or {
    choice {
        assume true;
    } or {
        havoc y;
    }
    x := x-1;
}
y := y * 2;
```

An XSTS contains 3 sets of transitions, each having different semantics. During the operation of the system the transitions to be executed are selected from the sets of inner and environmental transitions in an alternating manner. Transitions from the set of inner transitions are only selected for execution once, at the beginning.
This means that the transitions of the system will fire in the following order:
```
<init>
<env>
<inner>
<env>
<inner>
<env>
...
```
Where `<init>`, `<env>` and `<inner>` refer to transitions selected from the corresponding sets.

#### Inner transitions

Inner transitions describe the behaviour of the system. The set of inner transitions can be declared the following way:

```
trans {
    <statement>
    ... 
    <statement>
} or {
    <statement>
    ...
    <statement>
}
```

Each branch is interpreted as a separate transition.

#### Environmental transitions

Environmental transitions are used to describe the environment's effect on the system, for example incoming and outgoing events.

```
env {
    <statement>
    ... 
    <statement>
} or {
    <statement>
    ...
    <statement>
}
```

If you do not wish to use environmental transitions in your system, then leave the brackets empty: `env {}` This will result in a skip statement, which does nothing.

#### Init transitions

Init transitions are used to express more complex initialization steps that cannot be expressed using the initial values assigned in variable declarations. Please note that init transitions alone are not sufficient to express the initial states of a system, the initial values of the variable declarations alone have to describe a valid state of the system. 

```
init {
    <statement>
    ... 
    <statement>
} or {
    <statement>
    ...
    <statement>
}
```

If you do not wish to use environmental transitions in your system, then leave the brackets empty: `init {}` This will result in a skip statement, which does nothing.

### Property expression

The invariant that holds in every state of a correct model can be described the following way, where `<expr>` is a boolean expression:

```
prop {
    <expr>
}
```

If a state in which this expression does not hold is reachable from any of the initial states, then the model is unsafe.

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
prop {
    x>=0
}
```

A different example:

```
type Main_region : { __Inactive__, Normal, Error}
var signal_alert_Out : boolean = false
var signal_step_In : boolean = false
var main_region : Main_region = __Inactive__


trans {
    assume (main_region == Normal && signal_step_In == true);
    main_region := Error;
    signal_alert_Out := true;
} or {
    assume (main_region == Error && signal_step_In == true);
    main_region := Normal;
} or {
    assume (!(main_region == __Inactive__) && !((main_region == Normal && signal_step_In == true) || (main_region == Error && signal_step_In == true)));
}


init {
    main_region := Normal;
}

env {
    choice {
    	signal_step_In := true;
    } or {
    	signal_step_In := false;
    }
    signal_alert_Out := false;
}
```

This is equivalent to the following state machine:

![State machine](state_machine.png)

Note how incoming and outgoing events are described as boolean variables and handled in environmental transitions.
