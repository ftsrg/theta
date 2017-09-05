# Tools

Tools are concrete instantiations of the framework to solve a certain problem. Currently, the following 3 tools are available:

* `theta-cfa`: Reachability checking of error locations in Control Flow Automata (CFA) using CEGAR-based algorithms.
* `theta-sts`: Verification of safety properties in Symbolic Transition Systems (STS) using CEGAR-based algorithms.
* `theta-xta`: Verification of Uppaal timed automata (XTA).

## Building the tools

Thanks to the Gradle Wrapper, no installation is required. The projects can be simply built from the command line using `gradlew.bat [param]` (Windows) or `gradlew [param]` (Linux), where `[param]` should be `theta-cfa`, `theta-sts` or `theta-xta`. The jar files will appear in the directory _hu.bme.mit.theta.tools/build/libs_. The tools may require some dll or so files. These can be found in the _lib_ directory.

## Running the tools

The tools can be run with Java (JRE) 8 using the command `java -jar [name of the tool]`. If no arguments (or improper arguments) are given, the tools will display a help screen about their arguments and usage. Example input models can be found in the directory `hu.bme.mit.theta.formalism.cfa/src/test/resources` (similarly for sts and xta).
