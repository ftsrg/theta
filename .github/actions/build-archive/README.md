# Submission of TOOL_NAME to SV-COMP

_Theta_ is a generic, modular and configurable model checking framework developed at the [Critical Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.
Theta can both serve as a model checking backend, and also includes ready-to-use, stand-alone tools.

## Submitted version

The submitted version can be found under the `COMMIT_ID` commit in the [GitHub repository](https://github.com/ftsrg/theta/commit/COMMIT_ID).

Minimal necessary packages for Ubuntu 24.04 LTS:

* openjdk-17-jre-headless
* libgomp1
* libmpfr-dev

## Contents of the Submission
```
.
├── CONTRIBUTORS.md - contains information on the main contributors to TOOL_NAME
├── LIB_LICENSES.md - contains the licensing information for packaged dependencies
├── LICENSE - contains the license for TOOL_NAME
├── README.md - this file
├── lib - contains the native library dependencies
├── solvers - contains further dependencies (SMT-solvers), each having their respective licenses 
├── theta-smtlib.jar - the jarfile for installing and managing smt solvers (not necessary unless different solver versions are required)
├── SCRIPTNAME - the starting script of TOOL_NAME
├── input.c - the input file for the smoketest
├── smoketest.sh - the smoketest
└── theta.jar - the main jarfile of TOOL_NAME
```

## Usage
This packaged version of TOOL_NAME is equipped with the necessary SMT solvers, libraries and binary version of TOOL_NAME. To use it, one has to simply execute `theta-start.sh` with the desired parameters. The first parameter must be the name of the input task (except when using `--version`). The script provides the `--smt-home` directory to TOOL_NAME.
The tool is used with the following parameters on SV-COMP:

```
INPUT_FLAG \
--witness-only \
--loglevel RESULT
```

For a more verbose output, change `--loglevel` to `MAINSTEP, SUBSTEP, INFO or DETAIL`.
For more parameters, check out [the documentation on CEGAR](https://github.com/ftsrg/theta/blob/master/doc/CEGAR-algorithms.md) *(might not be up to date on every parameter, but gives a detailed explanation on them)* and [the main class of the XCFA frontend](https://github.com/ftsrg/theta/blob/master/subprojects/xcfa/xcfa-cli/src/main/java/hu/bme/mit/theta/xcfa/cli/stateless/XcfaCli.java).