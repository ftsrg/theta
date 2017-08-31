# Architecture

## Overview

Theta consists of the following main parts.
* **Formalisms and language front-ends**  
`hu.bme.mit.theta.core`, `hu.bme.mit.theta.formalism.*`, `hu.bme.mit.theta.frontend.*`  
Formalisms are usually low level, mathematical representations based on first order logic expressions and graph like structures. Formalisms can also support higher level languages that can be mapped to that particular formalism by a language front-end (consisting of a specific parser and possibly reductions for simplification of the model).
* **Analysis back-end**  
`hu.bme.mit.theta.analysis.*`  
The analysis back-end provides the verification algorithms. There is an interpreter for each formalism, providing a common interface towards the algorithms. This ensures that the algorithms work for all formalisms that provide an interpreter. The verification algorithms are mostly based on abstraction. The analysis back-end defines various abstract domains, strategies for performing abstraction and refinement, and algorithms built from these components.
* **SMT solver interface and SMT solvers**  
`hu.bme.mit.theta.solver.*`   
The framework provides a general SMT solver interface that supports incremental solving, unsat cores, and the generation of binary and sequence interpolants. The solver interface can be used for the implementation of analysis components. Currently, the interface is implemented by the SMT solver Z3, but it can easily be extended with new solvers.
* **Common projects**  
`hu.bme.mit.theta.common`  
Generic data structures and utilities.
* **Tools**  
`hu.bme.mit.theta.tools`  
Tools are command line (or GUI) applications that can be built into a runnable jar file. Tools usually read some input and then instantiate and run the algorithms.

Each project contains a README.md in its root directory describing its purpose in more detail.
