# Building Theta

Theta uses Java (JDK) 17 with [Gradle 7.4](https://gradle.org/) as a build system.
Currently, we use [OpenJDK 17](https://openjdk.java.net/projects/jdk/17/) (see instructions for [Windows](https://java.tutorials24x7.com/blog/how-to-install-openjdk-17-on-windows) and [Ubuntu](https://www.linuxuprising.com/2019/04/install-latest-openjdk-12-11-or-8-in.html)).
We are developing Theta on Linux, Windows and MacOS _(10.15.7)_.
Currently, floating point types are only fully supported on Linux and MacOS. Windows support is experimental and can cause cryptic exceptions to occur in native code. 
Theta can be built from the command line, but you can also import it into [IntelliJ IDEA](https://www.jetbrains.com/idea/).
Unfortunately, Eclipse [does not support](https://github.com/eclipse/buildship/issues/222) Gradle projects with Kotlin build scripts (yet).

## Dependencies

Theta has some external dependencies that may need to be obtained/installed depending on what parts of the framework you are working with.

**Z3 SMT Solver:**
The libraries for the Z3 solver (version 4.5.0) are included in the _lib_ directory, for Windows, Ubuntu (64 bit) and MacOS.
However, on Windows, _libz3.dll_ also requires some libraries from the [Microsoft Visual C++ Redistributable package](https://www.microsoft.com/en-us/download/details.aspx?id=48145) that we could not include due to licensing.
Install it, or just execute `Download-VCredist.ps1`, which will download the required libraries.
On MacOS, _libz3.dylib_ and _libz3java.dylib_ need to be on `DYLD_LIBRARY_PATH`.
If you have a different OS, you should download the appropriate [Z3 binary for version 4.5.0](https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0).
These libraries should be available on `PATH` for the executable tools.

*Troubleshooting*:
* If Z3 gives an assertion error (unreachable code reached), your Z3 version may not be correct.

**MPFR:**
For floating point support on MacOS, _libmpfr_java-1.4.jnilib_ and _libmpfr.dylib_ (as _libmpfr.4.dylib_) need to be on `DYLD_LIBRARY_PATH`. Additionally, _libmpfr_java-1.4.jnilib_ needs to linked as _libmpfr_java.jnilib_ onto both `DYLD_LIBRARY_PATH` and `java.library.path`.

**GraphViz:**
Theta can export graphs in _dot_ format and automatically convert them to images.
For this, [GraphViz](http://www.graphviz.org/) has to be installed and _dot_ (or _dot.exe_ on Windows) has to be on the `PATH`.

## Building from the command line

Theta can be built from the command line by simply executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux) from the root of the repository, where `build` is the name of the task that will compile all projects and run the tests.
On Linux make sure you _do not_ use `gradle build` as it executes your globally installed Gradle tool which might not be the appropriate version.
