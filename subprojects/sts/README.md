## Overview

This project contains the Symbolic Transition System (STS) formalism.
It is a generic, low-level formalism that can describe any kind of system using variables and initial/transition expressions.
The project includes:
* Classes to represent STSs.
* A domain specific language (DSL) to parse STSs from a textual representation.
* A frontend that can parse systems described in the [AIGER](http://fmv.jku.at/aiger/) (And-Inverter Graph) format and represent them using STSs.

### Related projects

* [`sts-analysis`](../sts-analysis/README.md): STS specific analysis modules enabling the algorithms to operate on them.
* [`sts-cli`](../sts-cli/README.md): An executable tool (command line) for running analyses on STSs.

## STS Formalism

An STS is a tuple `(V, I, T, P)` of

* variables `V = {v1, v2, ..., vn}`,
* an initial expression `I` over `V` describing the initial states,
* a transition expression `T` (over the variables `V` and their primed version `V'`) describing the transition relation, where the plain variables correspond to the actual state, while the primed variables correspond to the next state, and
* a property expression `P` over the variables `V`.

Algorithms are usually interested in proving that the property holds for every reachable state (safety property).

Variables of the STS can have the following types.
- `bool`: Booleans.
- `int`: Mathematical, unbounded SMT integers.
- `rat`: Rational numbers (implemented as SMT reals).
- `[K] -> V`: SMT arrays (associative maps) from a given key type `K` to a value type `V`.

Expressions of the STS include the following.
- Identifiers (variables).
- Primed expressions (only in transition expression) to represent the next state, e.g., `x'`.
- Literals, e.g., `true`, `false` (Bool), `0`, `123` (integer), `4 % 5` (rational).
- Comparison, e.g., `=`, `/=`, `<`, `>`, `<=`, `>=`.
- Boolean operators, e.g., `and`, `or`, `xor`, `not`, `imply`, `iff`.
- Arithmetic, e.g., `+`, `-`, `/`, `*`, `mod`, `rem`.
- Conditional: `if . then . else .`
- Array read (`a[i]`) and write (`a[i <- v]`).

### Textual Representation (DSL)

An example STS realizing a counter:

```
specification Counter {
    property P : {	
        var x : int
        initial x = 0
        transition if x < 10 then x' = x + 1 or x' = 0 else x' = 0
    } models G(x <= 10)
}
```

Variables can be defined by `var <NAME> : <TYPE>`, the initial formula by `initial <EXPRESSION>`, the transition formula by `transition <EXPRESSION>` and the property by `models G(<EXPRESSION>)`.

See _src/test/resources_ for more examples and _src/main/antlr_ for the full grammar.

### AIGER Frontend

The AIGER frontend can parse _aag_ (version 1.7) files into STSs.
Some utilities are also available, such as visualization and reductions.
For more information on the format, see the [webpage of AIGER](http://fmv.jku.at/aiger/).