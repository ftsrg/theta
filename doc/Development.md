# Development guide

Theta is written in Java 11 using
* [Gradle](https://gradle.org/) as a build system,
* [Git](https://git-scm.com/) and [GitHub](https://github.com/FTSRG/theta) for version control,
* [Travis](https://travis-ci.org/FTSRG/theta) for continuous integration,
* [Codacy](https://www.codacy.com/app/FTSRG/theta/dashboard) for static code analysis.

## Forking the repository

As the main repository is read-only, we suggest you to create your own [fork](https://help.github.com/articles/fork-a-repo/). Within your fork, we also recommend to create new _branches_ for your development. This enables us later on to easily integrate your work into the main repository by using [pull requests](https://help.github.com/articles/about-pull-requests/).

As the framework is under development, we suggest you to [sync your fork](https://help.github.com/articles/syncing-a-fork/) often and merge the master branch into your development branch(es).

## Building

See [Build.md](Build.md).

## Developing in IntelliJ IDEA

- Theta can be imported into [IntelliJ IDEA](https://www.jetbrains.com/idea/) as an existing Gradle project by selecting the _build.gradle.kts_ file in the root of the repository.
- If you want to build the whole project (and not just run a single test for example), make sure to run the _build task of the whole project_. This can be done by opening the Gradle tab, and then selecting _theta / theta / Tasks / build / build_, right clicking and selecting _Run_.
- [Import](https://www.jetbrains.com/help/idea/copying-code-style-settings.html) _doc/ThetaIntelliJCodeStyle.xml_ as a code style scheme for Java so that your formatting settings are consistent with the rest of the project.

## Coding conventions

See [Coding-conventions.md](Coding-conventions.md).
