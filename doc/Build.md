# Building Theta

Theta is uses Java 11, therefore JDK 11 is required to build Theta.
Currently, we use [OpenJDK 11](https://openjdk.java.net/projects/jdk/11/) (see instructions for [Windows](https://stackoverflow.com/questions/52511778/how-to-install-openjdk-11-on-windows) and [Ubuntu](https://www.linuxuprising.com/2019/01/how-to-install-openjdk-11-in-ubuntu.html)).
We are mainly developing on Windows, but we also test Theta on Linux.
Theta can be built from the command line, but you can also import it into [IntelliJ IDEA](https://www.jetbrains.com/idea/).
Unfortunately, Eclipse [does not support](https://github.com/eclipse/buildship/issues/222) Gradle projects with Kotlin build scripts (yet).

## Dependencies

Theta has some external dependencies that may need to be obtained/installed depending on what parts of the framework you are working with.

**Z3 SMT Solver:**
The libraries for the Z3 solver are included in the _lib_ directory, both for Windows and Ubuntu (64 bit).
However, on Windows, _libz3.dll_ also requires some libraries from the [Microsoft Visual C++ Redistributable package](https://www.microsoft.com/en-us/download/details.aspx?id=48145).
Install it, or just execute `Download-VCredist.ps1`, which will download the required libraries.
If you have a different OS, you should download the appropriate [Z3 release](https://github.com/Z3Prover/z3/releases).
These libraries should be available on `PATH` for tools.

**GraphViz:**
Theta can export graphs in _dot_ format and automatically convert them to images.
For this, [GraphViz](http://www.graphviz.org/) has to be installed and _dot_ (or _dot.exe_ on Windows) has to be on the `PATH`.

## Building from the command line

Theta can be built from the command line by simply executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux), where `build` is the name of the task that will compile all projects and run the tests.
