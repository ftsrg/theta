# Theta

[![Build Status](https://travis-ci.org/FTSRG/theta.svg?branch=master)](https://travis-ci.org/FTSRG/theta)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bc5270fd2ba2412bb5f4b81b42d4b9f8)](https://www.codacy.com/app/tothtamas28/theta?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=FTSRG/theta&amp;utm_campaign=Badge_Grade)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)

## About

_Theta_ is a generic, modular and configurable model checking framework developed at the [Fault Tolerant Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement. If you want to read more, take a look at the [list of publications](http://home.mit.bme.hu/~hajdua/theta/).

## Get Theta

* Clone the repository.
* Build the projects from the command line by executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux) from the root directory.
* On Windows, some libraries are required from the [Microsoft Visual C++ Redistributable package](https://www.microsoft.com/en-us/download/details.aspx?id=48145). Install it, or just go into the `lib` folder and execute `Download-VCredist.ps1`, which will download the required libraries.

## Use Theta

If you want to use the existing algorithms and tools defined in Theta, then take look at [doc/Tools.md](doc/Tools.md).

## Extend Theta

If you want to extend Theta and build your own algorithms and tools, then take look at [doc/For-developers.md](doc/For-developers.md), [doc/Architecture.md](doc/Architecture.md) and [Coding-conventions.md](doc/Coding-conventions.md).
