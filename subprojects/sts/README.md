## Overview

This project contains the Symbolic Transition System (STS) formalism. It is a generic, low-level formalism that can describe any kind of system using variables and initial/transition expressions. The project includes:

* Classes to represent STSs.
* A domain specific language (DSL) to parse STSs from a textual representation.
* A frontend that can parse systems described in the [AIGER](http://fmv.jku.at/aiger/) (And-Inverter Graph) format and represent them using STSs.

### Related projects

* [`sts-analysis`](../sts-analysis/README.md): STS specific analysis modules enabling the algorithms to operate on them.
* [`sts-cli`](../sts-cli/README.md): An executable tool (command line) for running analyses on STSs.

## STS Formalism

STSs consist of

* Variables,
* an initial expression describing the initial states,
* a transition expression (over the variables and their primed version) describing the transition relation, where the plain variables correspond to the actual state, while the primed variables correspond to the next state, and
* a property expression.

Algorithms are usually interested in proving that the property holds for every reachable state (safety property).

### Textual Representation (DSL)

An example STS realizing a counter:

```
specification Counter {
    property P : {	
        var x : integer
        initial x = 0
        transition if x < 10 then x' = x + 1 or x' = 0 else x' = 0
    } models G(x <= 10)
}
```

See _src/test/resources_ for more examples and _src/main/antlr_ for the full grammar.

### AIGER Frontend

The AIGER frontend can parse _aag_ (version 1.7) files into STSs. Some utilities are also available, such as visualization and reductions. For more information on the format, see the [webpage of AIGER](http://fmv.jku.at/aiger/).