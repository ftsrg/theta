# Building Theta

Theta uses Java (JDK) 21 with [Gradle 7.4](https://gradle.org/) as a build system.
Currently, we use [OpenJDK 21](https://openjdk.java.net/projects/jdk/21/) (see instructions for [Windows](https://java.tutorials24x7.com/blog/how-to-install-openjdk-21-on-windows) and [Ubuntu](https://www.linuxuprising.com/2019/04/install-latest-openjdk-12-11-or-8-in.html)).
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
On MacOS, the _lib_ directory containing the Z3 dynamic libraries (`.dylib` files) needs to be on `DYLD_LIBRARY_PATH`.
If you have a different OS, you should download the appropriate [Z3 binary for version 4.5.0](https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0).
These libraries should be available on `PATH` for the executable tools.

*Troubleshooting*:
* If Z3 gives an assertion error (unreachable code reached), your Z3 version may not be correct.

**GraphViz:**
Theta can export graphs in _dot_ format and automatically convert them to images.
For this, [GraphViz](http://www.graphviz.org/) has to be installed and _dot_ (or _dot.exe_ on Windows) has to be on the `PATH`.

## Building from the command line

Theta can be built from the command line by simply executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux) from the root of the repository, where `build` is the name of the task that will compile all projects and run the tests.
On Linux make sure you _do not_ use `gradle build` as it executes your globally installed Gradle tool which might not be the appropriate version.

## Building and running Theta on Windows

As highlighted above (and even more in reality), building Theta on Windows can be tricky (mostly due to Z3 dependencies). Considering Windows Subsystem for Linux (WSL), there are the following workflow options:

| Build   | Run     | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
|---------|---------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Windows | Windows | Try the above instructions, but be prepared to debug issues with native libraries.                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| WSL     | WSL     | Build&run should work fine as on Linux. However, it is our experience that Gradle is much slower in WSL.                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Windows | WSL     | The inconveniences of the above two options motivate this hybrid configuration. However, having java classpath issues is likely. We suggest two solutions:<br/><ul><li>Run the `shadowJar` task to build a fat jar that includes all dependencies. Drawback: `shadowJar` is slow and produces the large fat jar.</li><li>Run the `wslJar` task that configures the manifest file with a working classpath on WSL. **_This method is suggested for developing Theta on Windows_** if you do not want to suffer with Z3 dependencies. |

For the WSL options, we suggest a WSL2 installation with an Ubuntu distribution.
