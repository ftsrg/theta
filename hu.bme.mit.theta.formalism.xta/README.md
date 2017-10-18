## Overview

This project contains the Uppaal timed automata (XTA) formalism. Its main purpose is to describe timed systems as graphs with clock variables. A domain specific language (DSL) is available to parse XTAs from the textual representation of Uppaal. The project contains:

* Classes to represent XTAs.
* A domain specific language (DSL) to parse XTAs from a textual representation.
* XTA specific analysis modules enabling the algorithms to operate on them.
* An executable tool (command line and GUI) for running analyses on XTAs.

## Tool

Use one of the following commands to build the tool.

- Linux, command line: `./gradlew theta-xta-cli`
- Linux, GUI: `./gradlew theta-xta-gui`
- Windows, command line: `gradlew.bat theta-xta-cli`
- Windows, GUI: `gradlew.bat theta-xta-gui`

The runnable file will appear under _build/libs_. The tool also requires [GraphViz](../doc/Dependencies.md).

The command line tool can be run with `java -jar theta-xta-cli.jar [arguments]`. If no arguments are given, a help screen is displayed about the arguments and their possible values.

The GUI tool can be run simply by executing `theta-xta-gui.jar`. Use the controls to load the model, adjust parameters and run the algorithm.