# For developers

Theta is written in Java 8 using [Gradle](https://gradle.org/) as a build system and [Git](https://git-scm.com/) for version control. We are developing both on Windows and Linux. Theta can be built from command line, but you can most likely also import it into your favorite IDE.

## Recommended development workflow

As the main repository is read-only, we suggest you to create your own [fork](https://help.github.com/articles/fork-a-repo/). Within your fork, we also recommend to create new _branches_ for your development. This enables us later on to easily integrate your work into the main repository by using [pull requests](https://help.github.com/articles/about-pull-requests/).

As the framework is under development, we suggest you to [sync your fork](https://help.github.com/articles/syncing-a-fork/) often and merge the master branch into your development branch(es).

## Building from the command line
Thanks to the Gradle Wrapper, no installation is required. The projects can be simply built from the command line by executing `gradlew.bat build` (Windows) or `./gradlew build` (Linux) from the root directory.

## Importing and developing in Eclipse

The projects are currently developed and tested with [Oxygen](https://www.eclipse.org/oxygen/).
* We recommend downloading the [_Eclipse IDE for Java Developers_ package](https://www.eclipse.org/downloads/eclipse-packages/), as it contains a Git client and Gradle integration.
* If Gradle integration is not part of your installed Eclipse, install it from the _Eclipse Marketplace_, e.g. the _Buildship: Eclipse Plug-ins for Gradle_ (search for _Buildship Gradle Integration_).
  * _Optional: Also install the Eclipse Groovy tooling from <https://github.com/groovy/groovy-eclipse/wiki>._
* Add your fork (or the main repository) to Eclipse in the _Git Repositories_ window.
* To import the projects, choose _File / Import..._ / _Git_ / _Projects from Git_, then choose _Existing local repository_, select the repository and just use the default settings for the rest of the import process.
* At this point the projects may contain errors (due to some files not being generated). Open a console at the repository root directory and type `./gradlew build` on Linux or `gradlew.bat build` on Windows. After the `BUILD SUCCESSFUL` message, refresh the projects in Eclipse.
* If you use the Z3 solver, open the project `hu.bme.mit.theta.solver.z3` and right click on `com.microsoft.z3.jar` under _Project and External Dependencies_. Select _Build path_ / _Configure Build Path..._ and on the _Libraries_ tab select the _Native library location_ entry under _Project and External Dependencies_. Click on _Edit_ and browse the _lib_ folder that is in the root directory of the repository.
* There is a code formatting profile (ThetaFormatterProfile.xml) in this directory. In Eclipse, go to _Window_ / _Preferences_ / _Java_ / _Code Style_ / _Formatter_ and import the profile. You can enable automatic formatting on save under _Java_ / _Editor_ / _Save Actions_.
