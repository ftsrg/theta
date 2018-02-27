# Theta

[![Build Status](https://travis-ci.org/FTSRG/theta.svg?branch=master)](https://travis-ci.org/FTSRG/theta)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bc5270fd2ba2412bb5f4b81b42d4b9f8)](https://www.codacy.com/app/tothtamas28/theta?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=FTSRG/theta&amp;utm_campaign=Badge_Grade)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)

## About

_Theta_ is a generic, modular and configurable model checking framework developed at the [Fault Tolerant Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.

## Overview of the architecture

Theta can be divided into the following four layers.

* **Formalisms**: The core elements of Theta are the formalisms, which represent models of real life systems (e.g., software, hardware, protocols). Formalisms are usually low level, mathematical representations based on first order logic expressions and graph like structures. Formalisms can also support higher level languages that can be mapped to that particular formalism by a language front-end (consisting of a specific parser and possibly reductions for simplification of the model). The common features of the different formalisms reside in the `hu.bme.mit.theta.core` project (e.g., expressions) and each formalism has its own project. Currently, there are three formalisms: symbolic transition systems (`sts`), control-flow automata (`cfa`) and timed automata (`xta`).
* **Analysis back-end**: The analysis back-end provides the verification algorithms that can formally prove whether a model meets certain requirements. There is an interpreter for each formalism, providing a common interface towards the algorithms (e.g., calculating initial states and successors). This ensures that most components of the algorithms work for all formalisms (as long as they provide the interpreter). The verification algorithms are mostly based on abstraction. The analysis back-end defines various abstract domains, strategies for performing abstraction and refinement, and algorithms built from these components. The common components reside in the `hu.bme.mit.theta.analysis` project (e.g., CEGAR loop) and the formalism-specific modules (e.g., the interpreters) are implemented in the project of the given formalism.
* **SMT solver interface and SMT solvers**: Many components of the algorithm rely on satisfiability modulo theories (SMT) solvers. The framework provides a general SMT solver interface in the project `hu.bme.mit.theta.solver` that supports incremental solving, unsat cores, and the generation of binary and sequence interpolants. Currently, the interface is implemented by the SMT solver [Z3](https://github.com/Z3Prover/z3) in the project `hu.bme.mit.theta.solver.z3`, but it can easily be extended with new solvers.
* **Tools**: Tools are command line or GUI applications that can be compiled into a runnable jar file. Tools usually read some input and then instantiate and run the algorithms. Tools are implemented in the project of the formalism on which they work.

The figure below shows the architecture and the projects (without the `hu.bme.mit.theta` prefix). Each project contains a README.md in its root directory describing its purpose in more detail.

![Architecture](doc/images/architecture.png)

## Use Theta

Tools are concrete instantiations of the framework to solve a certain problem using the built in algorithms. Currently, the following 3 tools are available. Follow the links for more information about each tool.

* [`theta-cfa`](hu.bme.mit.theta.cfa/README.md): Reachability checking of error locations in Control Flow Automata (CFA) using CEGAR-based algorithms.
* [`theta-sts`](hu.bme.mit.theta.sts/README.md): Verification of safety properties in Symbolic Transition Systems (STS) using CEGAR-based algorithms.
* [`theta-xta`](hu.bme.mit.theta.xta/README.md): Verification of Uppaal timed automata (XTA).

## Extend Theta

If you want to extend Theta and build your own algorithms and tools, then take look at [doc/For-developers.md](doc/For-developers.md) and [doc/Coding-conventions.md](doc/Coding-conventions.md).

## Read more

If you want to read more, take a look at the [list of publications](http://home.mit.bme.hu/~hajdua/theta/). A good starting point is our [tool paper](http://home.mit.bme.hu/~hajdua/theta/fmcad2017.pdf) and [slides](https://www.slideshare.net/AkosHajdu/theta-a-framework-for-abstraction-refinementbased-model-checking) presented at FMCAD 2017.

To cite Theta, please cite the following paper.

```
@inproceedings{theta-fmcad2017,
    author     = {T\'oth, Tam\'as and Hajdu, \'{A}kos and V\"or\"os, Andr\'as and Micskei, Zolt\'an and Majzik, Istv\'an},
    year       = {2017},
    title      = {Theta: a Framework for Abstraction Refinement-Based Model Checking},
    booktitle  = {Proceedings of the 17th Conference on Formal Methods in Computer-Aided Design},
    isbn       = {978-0-9835678-7-5},
    editor     = {Stewart, Daryl and Weissenbacher, Georg},
    pages      = {176--179},
}
```
