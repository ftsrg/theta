# For developers

Theta is written in Java 8 using
* [Gradle](https://gradle.org/) as a build system,
* [Git](https://git-scm.com/) and [GitHub](https://github.com/FTSRG/theta) for version control,
* [Travis](https://travis-ci.org/FTSRG/theta) for continuous integration,
* [Codacy](https://www.codacy.com/app/FTSRG/theta/dashboard) for static code analysis.

There are two ways to work with Theta. You can use the precompiled binaries as a _library_ in your own project (recommended), or you can also work with the _source code_ of Theta (only recommended for core developers).

## Use Theta as a library

TODO

## Work with the source code of Theta

We are mainly developing on Windows, but we also test Theta on Linux. Theta can be built from command line, but you can most likely also import it into your favorite IDE. Theta has some external [dependencies](Dependencies.md) that may need to be obtained/installed depending on what parts of the framework you are working with.

### Building from the command line

Theta can be built from the command line by simply executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux), where `build` is the name of the task that will compile all projects and run the tests.

### Recommended development workflow

As the main repository is read-only, we suggest you to create your own [fork](https://help.github.com/articles/fork-a-repo/). Within your fork, we also recommend to create new _branches_ for your development. This enables us later on to easily integrate your work into the main repository by using [pull requests](https://help.github.com/articles/about-pull-requests/).

As the framework is under development, we suggest you to [sync your fork](https://help.github.com/articles/syncing-a-fork/) often and merge the master branch into your development branch(es).

### Importing and developing in Eclipse

The projects are currently developed and tested with [Eclipse Oxygen](https://www.eclipse.org/oxygen/).
* We recommend downloading the [_Eclipse IDE for Java Developers_ package](https://www.eclipse.org/downloads/eclipse-packages/), as it contains a Git client and Gradle integration.
* If Gradle integration is not part of your installed Eclipse, install it from the _Eclipse Marketplace_, e.g. the _Buildship: Eclipse Plug-ins for Gradle_ (search for _Buildship Gradle Integration_).
  * _Optional: Also install the Eclipse Groovy tooling from <https://github.com/groovy/groovy-eclipse/wiki>._
* Add your fork (or the main repository) to Eclipse in the _Git Repositories_ window.
* To import the projects, choose _File / Import..._ / _Gradle_ / _Existing Gradle Project_, specify the root directory and use the default settings.
* At this point the projects may contain errors (due to some files not being generated). Build the projects from command line, and refresh the projects in Eclipse.
* If you use the Z3 solver, go to the properties of the `solver.z3` project, select _Java Build Path_ / _Libraries_ / _Project and External Dependencies_ / _Native library location_. Click on _Edit_ and browse the _lib_ folder that is located in the root of the repository. Alternatively, you can also add the _lib_ folder to the PATH.
  * On Windows, Z3 requires some additional libraries. See the [dependencies page](Dependencies.md) for more information.
* If there are access restriction errors in Eclipse due to JavaFX then either install the [e(fx)clipse plugin](http://www.eclipse.org/efxclipse) or go to the _Java Build Path_ in the properties of the project and under the _Libraries_ tab delete the JRE System Library and re-add it.
* There is a code formatting profile (ThetaFormatterProfile.xml) in this directory. In Eclipse, go to _Window_ / _Preferences_ / _Java_ / _Code Style_ / _Formatter_ and import the profile. You can enable automatic formatting on save under _Java_ / _Editor_ / _Save Actions_.

### Errors after updating your fork

It is possible that there will be _strange errors_ after updating your fork. You should perform the following steps to resolve them.

* Rebuild from the command line and refresh all projects in Eclipse (by simply selecting them and pressing F5). This should solve errors when some generated files are missing.
* In the context menu of the root project (`theta`) select _Gradle_ / _Refresh Gradle Project_. This should solve issues when the dependencies of the projects changed or projects have been added/deleted.
