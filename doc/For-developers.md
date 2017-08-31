# For developers

Theta is written in Java 8 using [Gradle](https://gradle.org/) as a build system. We are developing both on Windows and Linux.

## Preferred development workflow

As the main repository is read-only, we suggest you to create your own _fork_. Within your fork, we also recommend to create new _branches_ for your development. This enables us later on to easily integrate your work into the main repository by using _pull requests_.

As the framework is under development, we suggest you to sync your fork often and merge the master branch into your development branch(es). See [https://help.github.com/articles/syncing-a-fork/](https://help.github.com/articles/syncing-a-fork/).

## Building from the command line
Thanks to the Gradle Wrapper, no installation is required. The projects can be simply built from the command line using `gradlew.bat` (Windows) or `gradlew` (Linux).

## Importing to Eclipse

* The projects are currently developed and tested with **Eclipse Neon**.
* Install a Gradle Eclipse plugin from the **Eclipse Marketplace**, e.g. the **Buildship: Eclipse Plug-ins for Gradle** (search for _Buildship Gradle Integration_).
  * _Optional: Also install the Eclipse Groovy tooling from <https://github.com/groovy/groovy-eclipse/wiki>._
* To import the projects, choose **Import...** | **Gradle Project**, specify the root directory as the repository directory and import them with the default **Gradle distribution** (**Gradle wrapper (recommended)**).
* At this point the projects may contain errors (due to some files not being generated). Open a console at the repository root directory and type `./gradlew build` on Linux or `gradlew.bat build` on Windows. After the `BUILD SUCCESSFUL` message, refresh the projects in Eclipse.
* If you use the Z3 solver, open the project `hu.bme.mit.theta.solver.z3` and right click on `com.microsoft.z3.jar` under _Project and External Dependencies_. Select _Build path_ / _Configure Build Path..._ and on the _Libraries_ tab select the _Native library location_ entry under _Project and External Dependencies_. Click on _Edit_ and browse the _lib_ folder that is in the root directory of the repository.
* There is a code formatting profile (ThetaFormatterProfile.xml) in this directory. In Eclipse, go to _Window_ / _Preferences_ / _Java_ / _Code Style_ / _Formatter_ and import the profile. You enable automatic formatting on save under _Java_ / _Editor_ / _Save Actions_.