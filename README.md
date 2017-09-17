# Theta

[![Build Status](https://travis-ci.org/FTSRG/theta.svg?branch=master)](https://travis-ci.org/FTSRG/theta)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bc5270fd2ba2412bb5f4b81b42d4b9f8)](https://www.codacy.com/app/tothtamas28/theta?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=FTSRG/theta&amp;utm_campaign=Badge_Grade)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)

## About

_Theta_ is a generic, modular and configurable model checking framework developed at the [Fault Tolerant Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.

## Get Theta

* Clone the repository.
* Build the projects from the command line by executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux) from the root directory.
* On Windows, some libraries are required from the [Microsoft Visual C++ Redistributable package](https://www.microsoft.com/en-us/download/details.aspx?id=48145). Install it, or just go into the `lib` folder and execute `Download-VCredist.ps1`, which will download the required libraries.

## Use Theta

Tools are concrete instantiations of the framework to solve a certain problem using the built in algorithms. Currently, the following 3 tools are available. Follow the links for more information about each tool.

* [`theta-cfa`](hu.bme.mit.theta.formalism.cfa/README.md): Reachability checking of error locations in Control Flow Automata (CFA) using CEGAR-based algorithms.
* [`theta-sts`](hu.bme.mit.theta.formalism.sts/README.md): Verification of safety properties in Symbolic Transition Systems (STS) using CEGAR-based algorithms.
* [`theta-xta`](hu.bme.mit.theta.formalism.xta/README.md): Verification of Uppaal timed automata (XTA).

## Extend Theta

If you want to extend Theta and build your own algorithms and tools, then take look at [doc/For-developers.md](doc/For-developers.md), [doc/Architecture.md](doc/Architecture.md) and [Coding-conventions.md](doc/Coding-conventions.md).

## Read more

If you want to read more, take a look at the [list of publications](http://home.mit.bme.hu/~hajdua/theta/). A good starting point is our [tool paper](http://home.mit.bme.hu/~hajdua/theta/fmcad2017.pdf) presented at FMCAD 2017.

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