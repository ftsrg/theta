## Overview

This project contains the Symbolic Transition System (STS) formalism. It is a generic, low-level formalism that can describe any kind of system using variables and initial/transition expressions. The project includes:

* Classes to represent STSs.
* A domain specific language (DSL) to parse STSs from a textual representation.
* A frontend that can parse systems described in the [AIGER](http://fmv.jku.at/aiger/) (And-Inverter Graph) format and represent them using STSs.
* STS specific analysis modules enabling the algorithms to operate on them.
* An executable tool for running analyses on STSs.

## STS Formalism

STSs consist of

* A set of variables,
* an initial expression (over the variables) describing the initial states,
* a transition expression (over the variables and their primed version) describing the transition relation, where the plain variables correspond to the actual state, while the primed variables correspond to the next state, and
* a property expression (over the variables) that must hold in every state (safety property).

### Textual Representation

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

### AIGER Frontend

The AIGER frontend can parse _aag_ (version 1.7) files into STSs. For more information, see the [webpage of AIGER](http://fmv.jku.at/aiger/).

## Tool

The tool can be built using the command `./gradlew theta-sts` (Linux) or `gradle.bat theta-sts` (Windows). The runnable file will appear under _build/libs_. The tool also requires the libraries in the _../lib_ folder (if you work on Windows, also read the README there).

The tool can be run with `java -jar theta-sts.jar [arguments]`. If no arguments are given, a help screen is displayed about the arguments and their possible values. For example, put the example above in a file called `counter.system` and call `java -jar theta-sts.jar -m counter.system -d EXPL -r SEQ_ITP -ll 3`.