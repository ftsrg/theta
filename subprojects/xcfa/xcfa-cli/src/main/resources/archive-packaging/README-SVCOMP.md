# Submission of TOOL_NAME to SV-COMP

_Theta_ is a generic, modular and configurable model checking framework developed at the [Critical Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.
Theta can both serve as a model checking backend, and also includes ready-to-use, stand-alone tools.

## Submitted version

The submitted version can be found under the `VERSION` tag in the [GitHub repository](https://github.com/ftsrg/theta/releases/tag/VERSION).

Minimal necessary packages for Ubuntu 24.04 LTS:

* openjdk-21-jre-headless
* libgomp1
* libmpfr-dev

## Contents of the Submission

CONTENTS

## Usage
This packaged version of TOOL_NAME is equipped with the necessary SMT solvers, libraries and binary version of TOOL_NAME. To use it, one has to simply execute `theta-start.sh` with the desired parameters. The first parameter must be the name of the input task (except when using `--version`). The script provides the `--smt-home` directory to TOOL_NAME.
The tool is used with the following parameters on SV-COMP:

```
--input <input-file> \
--property <property-file> \
INPUT_FLAG
```

For a more verbose output, change `--loglevel` to `MAINSTEP, SUBSTEP, INFO or DETAIL`.
For more parameters, check out [the documentation on CEGAR](https://github.com/ftsrg/theta/blob/master/doc/CEGAR-algorithms.md) *(might not be up to date on every parameter, but gives a detailed explanation on them)* and [the main class of the XCFA frontend](https://github.com/ftsrg/theta/blob/master/subprojects/xcfa/xcfa-cli/src/main/java/hu/bme/mit/theta/xcfa/cli/XcfaCli.kt).

## License

The _Theta_ tool is licensed under Apache-2.0.
The utilized SMT solvers may fall under different licenses, these can be found in the corresponding subfolders.