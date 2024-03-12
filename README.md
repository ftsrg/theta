# Theta

![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/build-Linux/badge.svg)
![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/build-Windows/badge.svg)
![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/build-macOS/badge.svg)
![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/test-Linux/badge.svg)
![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/test-Windows/badge.svg)
![](https://raw.githubusercontent.com/ftsrg/theta/badges/badges/test-macOS/badge.svg)

[![](https://img.shields.io/docker/v/ftsrg/theta-cfa-cli?label=cfa&logo=docker)](https://hub.docker.com/r/ftsrg/theta-cfa-cli/)
[![](https://img.shields.io/docker/v/ftsrg/theta-xsts-cli?label=xsts&logo=docker)](https://hub.docker.com/r/ftsrg/theta-xsts-cli/)
[![](https://img.shields.io/docker/v/ftsrg/theta-xcfa-cli?label=xcfa&logo=docker)](https://hub.docker.com/r/ftsrg/theta-xcfa-cli/)
[![](https://img.shields.io/docker/v/ftsrg/theta-xta-cli?label=xta&logo=docker)](https://hub.docker.com/r/ftsrg/theta-xta-cli/)
[![](https://img.shields.io/docker/v/ftsrg/theta-sts-cli?label=sts&logo=docker)](https://hub.docker.com/r/ftsrg/theta-sts-cli/)

[![Coverage](https://sonarcloud.io/api/project_badges/measure?project=ftsrg_theta&metric=coverage)](https://sonarcloud.io/summary/new_code?id=ftsrg_theta)
[![Maintainability Rating](https://sonarcloud.io/api/project_badges/measure?project=ftsrg_theta&metric=sqale_rating)](https://sonarcloud.io/summary/new_code?id=ftsrg_theta)
[![Quality Gate Status](https://sonarcloud.io/api/project_badges/measure?project=ftsrg_theta&metric=alert_status)](https://sonarcloud.io/summary/new_code?id=ftsrg_theta)
[![Check copyright](https://github.com/ftsrg/theta/actions/workflows/check-copyright.yml/badge.svg)](https://github.com/ftsrg/theta/actions/workflows/check-copyright.yml)
[![Check formatting](https://github.com/ftsrg/theta/actions/workflows/check-formatting.yml/badge.svg)](https://github.com/ftsrg/theta/actions/workflows/check-formatting.yml)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)

![Theta logo](https://raw.githubusercontent.com/ftsrg/theta/master/doc/theta-logo.png)

## About

_Theta_ is a generic, modular and configurable model checking framework developed at the [Critical Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.
Theta can both serve as a model checking backend, and also includes ready-to-use, stand-alone tools.

## Use Theta

Tools are concrete instantiations of the framework to solve a certain problem using the built-in algorithms.
Currently, the following tools are available (follow the links for more information).

* [`theta-cfa-cli`](subprojects/cfa/cfa-cli): Reachability checking of error locations in Control Flow Automata (CFA) using CEGAR-based algorithms.
  * [Gazer](https://github.com/ftsrg/gazer) is an [LLVM](https://llvm.org/)-based frontend to verify C programs using theta-cfa-cli, also giving support towards [SV-COMP](https://sv-comp.sosy-lab.org/2021/). See our [tool paper at TACAS](https://ftsrg.mit.bme.hu/theta/publications/tacas2021.pdf) for more information.
  * [PLCverif](https://cern.ch/plcverif) is a tool developed at CERN for the formal specification and verification of PLC (Programmable Logic Controller) programs, supporting theta-cfa-cli as one of its verification backends.
* [`theta-sts-cli`](subprojects/sts/sts-cli): Verification of safety properties in Symbolic Transition Systems (STS) using CEGAR-based algorithms.
  * theta-sts-cli natively supports the [AIGER format](http://fmv.jku.at/aiger/) of the [Hardware Model Checking Competition (HWMCC)](http://fmv.jku.at/hwmcc/).
* [`theta-xta-cli`](subprojects/xta/xta-cli): Verification of [Uppaal](http://www.uppaal.org/) timed automata (XTA).
* [`theta-xsts-cli`](subprojects/xsts/xsts-cli): Verification of safety properties in eXtended Symbolic Transition Systems (XSTS) using CEGAR-based algorithms.
  * [Gamma](https://github.com/ftsrg/gamma) is a statechart composition framework, that supports theta-xsts-cli as a backend to verify collaborating state machines.
  * theta-xsts-cli natively supports Petri net models in the [PNML](http://www.pnml.org/) format (experimental).
* [`theta-xcfa-cli`](subprojects/xcfa-old/xcfa-cli): Reachability checking of error locations in eXtended Control Flow Automata (XCFA) using CEGAR-based algorithms. The CFA formalism is extended with procedures and processes, able to support multithreaded analysis and also several optimization passes. Right now it is mainly used to check both single and multithreaded C programs.
  * the [`c-frontend`](subprojects/frontends/c-frontend) module of Theta is capable of parsing C programs and transforming them into a formalism independent, in-memory representation. The `xcfa-cli` is able to convert this representation into an XCFA.

To use Theta as a standalone tool, see the following deployments:
 * [DockerHub](https://hub.docker.com/u/ftsrg) and [ghcr.io](https://github.com/orgs/ftsrg/packages) for Docker images based on the `*-cli` subprojects
 * Latest [release](https://github.com/ftsrg/theta/releases/latest) for `.jar` files

To use Theta as a library, see [Maven Central](https://central.sonatype.com/namespace/hu.bme.mit.theta).


## Overview of the architecture

Theta can be divided into the following four layers.

* **Formalisms**: The core elements of Theta are the formalisms, which represent models of real life systems (e.g., software, hardware, protocols).
  Formalisms are usually low level, mathematical representations based on first order logic expressions and graph like structures.
  Formalisms can also support higher level languages that can be mapped to that particular formalism by a language front-end (consisting of a specific parser and possibly reductions for simplification of the model).
  The common features of the different formalisms reside in the [`core`](subprojects/common/core) project (e.g., expressions and statements) and each formalism has its own project.
  Currently, the following formalisms are supported: (extended) symbolic transition systems ([`sts`](subprojects/sts/sts) / [`xsts`](subprojects/xsts/xsts)), (extended) control-flow automata ([`cfa`](subprojects/cfa/cfa) / [`xcfa`](subprojects/xcfa/xcfa)) and timed automata ([`xta`](subprojects/xta/xta)).
* **Analysis back-end**: The analysis back-end provides the verification algorithms that can formally prove whether a model meets certain requirements.
  There is an interpreter for each formalism, providing a common interface towards the algorithms (e.g., calculating initial states and successors).
  This ensures that most components of the algorithms work for all formalisms (as long as they provide the interpreter).
  The verification algorithms are mostly based on abstraction.
  The analysis back-end defines various abstract domains (e.g., predicates, explicit values, zones), strategies for performing abstraction and refinement (e.g., interpolation), and algorithms built from these components.
  The common components reside in the [`analysis`](subprojects/common/analysis) project (e.g., CEGAR loop) and the formalism-specific modules (e.g., the interpreters) are implemented in separate analysis projects (with suffix `-analysis`) for each formalism.
* **SMT solver interface and SMT solvers**: Many components of the algorithms rely on satisfiability modulo theories (SMT) solvers.
  The framework provides a general SMT solver interface in the project [`solver`](subprojects/common/solver) that supports incremental solving, unsat cores, and the generation of binary and sequence interpolants.
  Currently, the interface is implemented by the [Z3](https://github.com/Z3Prover/z3) SMT solver in the project [`solver-z3`](subprojects/common/solver-z3), but it can easily be extended with new solvers.
* **Tools**: Tools are command line applications that can be compiled into a runnable jar file.
  Tools usually read some input and then instantiate and run the algorithms.
  Tools are implemented in separate projects, currently with the `-cli` suffix.

The table below shows the architecture and the projects.
Each project contains a README.md in its root directory describing its purpose in more detail.

|  | Common | CFA | STS | XTA | XSTS | XCFA |
|--|--|--|--|--|--|--|
| **Tools** | [`solver-smtlib-cli`](subprojects/solver/solver-smtlib-cli) | [`cfa-cli`](subprojects/cfa/cfa-cli) | [`sts-cli`](subprojects/sts/sts-cli) | [`xta-cli`](subprojects/xta/xta-cli) | [`xsts-cli`](subprojects/xsts/xsts-cli) | [`xcfa-cli`](subprojects/xcfa-old/xcfa-cli) |
| **Analyses** | [`analysis`](subprojects/common/analysis) | [`cfa-analysis`](subprojects/cfa/cfa-analysis) | [`sts-analysis`](subprojects/sts/sts-analysis) | [`xta-analysis`](subprojects/xta/xta-analysis) | [`xsts-analysis`](subprojects/xsts/xsts-analysis) | [`xcfa-analysis`](subprojects/xcfa-old/xcfa-analysis) |
| **Formalisms** | [`core`](subprojects/common/core), [`common`](subprojects/common/common) | [`cfa`](subprojects/cfa/cfa) | [`sts`](subprojects/sts/sts) | [`xta`](subprojects/xta/xta) | [`xsts`](subprojects/xsts/xsts) | [`xcfa`](subprojects/xcfa-old/xcfa) |
| **SMT solvers** | [`solver`](subprojects/solver/solver), [`solver-z3`](subprojects/solver/solver-z3), [`solver-smtlib`](subprojects/solver/solver-smtlib) | |

## Extend Theta

If you want to extend Theta and build your own algorithms and tools, then take look at [doc/Development.md](doc/Development.md).

## Read more

If you want to read more, take a look at [our list of publications](https://ftsrg.github.io/theta/publications/).
A good starting point is our [tool paper](https://ftsrg.github.io/theta/publications/fmcad2017.pdf) and [slides](https://www.slideshare.net/AkosHajdu/theta-a-framework-for-abstraction-refinementbased-model-checking)/[talk](https://oc-presentation.ltcc.tuwien.ac.at/engage/theodul/ui/core.html?id=c658c37e-ae70-11e7-a0dd-bb49f3cb440c) presented at FMCAD 2017.
Furthermore, our [paper in the Journal of Automated Reasoning](https://link.springer.com/content/pdf/10.1007%2Fs10817-019-09535-x.pdf) is a good overview of the algorithms in Theta.

To cite Theta as a tool, please use the following paper.

```
@inproceedings{theta-fmcad2017,
    author     = {T\'oth, Tam\'as and Hajdu, \'{A}kos and V\"or\"os, Andr\'as and Micskei, Zolt\'an and Majzik, Istv\'an},
    year       = {2017},
    title      = {Theta: a Framework for Abstraction Refinement-Based Model Checking},
    booktitle  = {Proceedings of the 17th Conference on Formal Methods in Computer-Aided Design},
    isbn       = {978-0-9835678-7-5},
    editor     = {Stewart, Daryl and Weissenbacher, Georg},
    pages      = {176--179},
    doi        = {10.23919/FMCAD.2017.8102257},
}
```

## Acknowledgements
Supporters of the Theta project are listed below.

* [MTA-BME Lendület Cyber-Physical Systems Research Group](http://lendulet.inf.mit.bme.hu/)
* [Fault Tolerant Systems Research Group](https://inf.mit.bme.hu/en), [Department of Measurement and Information Systems](https://www.mit.bme.hu/eng/), [Budapest University of Technology and Economics](http://www.bme.hu/?language=en)
* [Gedeon Richter’s](https://www.richter.hu/en-US/Pages/default.aspx) Talentum Foundation
* Nemzeti Tehetség Program, [Nemzet Fiatal Tehetségeiért Ösztöndíj 2016](http://www.emet.gov.hu/felhivasok/nemzeti_tehetseg_program212/) (NTP-NFTÖ-16)
* Nemzeti Tehetség Program, [Nemzet Fiatal Tehetségeiért Ösztöndíj 2018](http://www.emet.gov.hu/felhivasok/felhivas46/) (NTP-NFTÖ-18)
* [CECRIS project](http://www.cecris-project.eu/) (EU FP7 324334)
* [R5-COP project](http://www.r5-cop.eu/) (EU FP7 ARTEMIS 621447 and NRDI Fund NEMZ_12-1-2014-0003)
* [Arrowhead Tools project](https://www.arrowhead.eu/arrowheadtools) (EU ECSEL 826452 and NRDI Fund 2019-2.1.3-NEMZ_ECSEL-2019-00003)
