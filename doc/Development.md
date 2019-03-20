# Development guide

Theta is written in Java 11 using
* [Gradle](https://gradle.org/) as a build system,
* [Git](https://git-scm.com/) and [GitHub](https://github.com/FTSRG/theta) for version control,
* [Travis](https://travis-ci.org/FTSRG/theta) for continuous integration,
* [Codacy](https://www.codacy.com/app/FTSRG/theta/dashboard) for static code analysis.

There are two ways to work with Theta. You can use the precompiled binaries as a _library_ in your own project (recommended), or you can also work with the _source code_ of Theta.

## Use Theta as a library

**Not yet available.**
We had a [Bintray](https://bintray.com/ftsrg/maven/theta) deployment of the previous version of Theta.
We are working on upgrading this deployment to the current version.

## Work with the source code of Theta

### Forking the repository

As the main repository is read-only, we suggest you to create your own [fork](https://help.github.com/articles/fork-a-repo/). Within your fork, we also recommend to create new _branches_ for your development. This enables us later on to easily integrate your work into the main repository by using [pull requests](https://help.github.com/articles/about-pull-requests/).

As the framework is under development, we suggest you to [sync your fork](https://help.github.com/articles/syncing-a-fork/) often and merge the master branch into your development branch(es).

### Building

See [Build.md](Build.md).

### Developing in IntelliJ IDEA

- Theta can be imported into [IntelliJ IDEA](https://www.jetbrains.com/idea/) as an existing Gradle project by selecting the _build.gradle.kts_ file in the root of the repository.
- Make sure to [delegate build and run actions to Gradle](https://www.jetbrains.com/help/idea/gradle.html#delegate_build_gradle).
- [Import](https://www.jetbrains.com/help/idea/copying-code-style-settings.html) _doc/ThetaIntelliJCodeStyle.xml_ as a code style scheme for Java so that your formatting settings are consistent with the rest of the project.

### Coding conventions

See [Coding-conventions.md](Coding-conventions.md).