# Development guide

Theta is written in Java 11 using
* [Gradle](https://gradle.org/) as a build system,
* [Git](https://git-scm.com/) and [GitHub](https://github.com/FTSRG/theta) for version control,
* [Travis](https://travis-ci.org/FTSRG/theta) and [GitHub actions](https://github.com/ftsrg/theta/actions) for continuous integration,
* [Codacy](https://www.codacy.com/app/FTSRG/theta/dashboard) for static code analysis,
* [Docker](https://www.docker.com/) for packaging.

## Releases and versioning

Theta uses [semantic versioning](https://semver.org/) in a `MAJOR.MINOR.PATCH` format, e.g., `v1.2.3`.
Binaries are uploaded to major/minor [releases](https://github.com/ftsrg/theta/releases), but (currently) not for patches.
Any change that is not visible from the user's perspective (e.g., the frontends), should be a patch increment (e.g., bugfixes, small performance improvements).
Changes visible to the user (e.g., a new option in an algoritmh) should be at least minor increment, but if the change is big enough (e.g., new formalism, new tool) a major increment can be performed.
We usually develop on separate branches and increment the version number just before merging to the main branch.

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
