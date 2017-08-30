# Architecture

## Overview

Theta consists of the following 3 main parts and some common projects.
* **Formalisms and language front-ends**: Formalisms are usually low level, mathematical representations based on first order logic expressions and graph like structures. Formalisms can also support higher level languages that can be mapped to that particular formalism by a language front-end (consisting of a specific parser and possibly reductions for simplification of the model).
* **Analysis back-end**: The analysis back-end provides the verification algorithms. There is an interpreter for each formalism, providing a common interface towards the algorithms. This ensures that the algorithms work for all formalisms that provide an interpreter. The verification algorithms are mostly based on abstraction. The analysis back-end defines various abstract domains, strategies for performing abstraction and refinement, and algorithms built from these components.
* **SMT solver interface and SMT solvers**: The framework provides a general SMT solver interface that supports incremental solving, unsat cores, and the generation of binary and sequence interpolants. The solver interface can be used for the implementation of analysis components. Currently, the interface is implemented by the SMT solver Z3, but it can easily be extended with new solvers.

## Projects

Theta is written in Java 8 using [Gradle](https://gradle.org/) as a build system. We are developing both on Windows and Linux. Each project starts with the prefix `hu.bme.mit.theta`. The projects can be categorized as described by the architecture overview above.
* **Common** projects
  * `hu.bme.mit.theta.common`: This project provides common constructs and data structures such as logging and graph-based visualization.
  * `hu.bme.mit.theta.core`: This project provides classes and utilities to build and manipulate first order logic expressions. Classes include types, constants, variables, expressions, statements. Utilities include folding, unfolding, collecting atoms, collecting variables, etc.
  * `hu.bme.mit.theta.tools`: This project contains tools. Tools are command line (or GUI) applications that can be built into a runnable jar file. Tools usually read some input and then instantiate and run the algorithms.
* **Formalism** and **language front-end** projects
  * `hu.bme.mit.theta.formalism`: This project provides constructs and utilities that are common in the different formalisms.
  * `hu.bme.mit.theta.formalism.*`: There is a separate project for each formalism (e.g., `sts`, `cfa`, `xta`, ...) that defines the classes and utilities related to the formalism. Formalisms are usually based on the expressions and statements defined in the `core` project. For some formalisms, a domain specific language (DSL) is also available. Using the DSL, instances of the formalism can be read from a textual representation.
  * `hu.bme.mit.theta.frontend.*`: These projects provide transformations from external languages and formalisms to our internal formalisms. Currently, we support a mapping from AIGER format to our STS formalism.
* **Analysis back-end** projects
  * `hu.bme.mit.theta.analysis`: This projects contains the analysis algorithms and their components, e.g., abstract domains, abstract reachability graphs, refinement strategies, precisions, etc.
  * `hu.bme.mit.theta.analysis.*` There is a separate project for each formalism that contains the formalism-dependent parts of the algorithms, e.g., interpreter for the formalism.
* **SMT solver interface** and **SMT solver** projects
  * `hu.bme.mit.theta.solver`: This project provides a common interface over different SMT solvers. SMT solvers can be used to query satisfiability of expressions and to generate interpolants and unsat cores.
  * `hu.bme.mit.theta.solver.*`: There is a separate project for each solver (currently only `z3`) that wraps the solver to match the common interface. You should only use factories in these projects to create solvers and then use the common interfaces. This way, you can change the solver easily.