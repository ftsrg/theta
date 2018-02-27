## Overview

This project contains the Symbolic Transition System (STS) formalism. It is a generic, low-level formalism that can describe any kind of system using variables and initial/transition expressions. The project includes:

* Classes to represent STSs.
* A domain specific language (DSL) to parse STSs from a textual representation.
* A frontend that can parse systems described in the [AIGER](http://fmv.jku.at/aiger/) (And-Inverter Graph) format and represent them using STSs.
* STS specific analysis modules enabling the algorithms to operate on them.
* An executable tool (command line and GUI) for running analyses on STSs.

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

See _src/test/resources_ for more examples.

### AIGER Frontend

The AIGER frontend can parse _aag_ (version 1.7) files into STSs. Some utilities are also available, such as visualization and reductions. For more information on the format, see the [webpage of AIGER](http://fmv.jku.at/aiger/).

## Tool

Use one of the following commands to build the tool.

- Linux, command line: `./gradlew theta-sts-cli`
- Linux, GUI: `./gradlew theta-sts-gui`
- Windows, command line: `gradlew.bat theta-sts-cli`
- Windows, GUI: `gradlew.bat theta-sts-gui`

The runnable file will appear under _build/libs_. The tool also requires [Z3 and GraphViz](../doc/Dependencies.md).

The command line tool can be run with `java -jar theta-sts-cli.jar [arguments]`. If no arguments are given, a help screen is displayed about the arguments and their possible values. For example, put the example above in a file called `counter.system` and call `java -jar theta-sts-cli.jar --model counter.system --domain EXPL --refinement SEQ_ITP --loglevel INFO`.

The GUI tool can be run simply by executing `theta-sts-gui.jar`. Use the controls to load the model, adjust parameters and run the algorithm. _Note, that the AIGER frontend is only supported by the command line tool._