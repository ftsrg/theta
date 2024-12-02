# Development guide

Theta is written in Java 17 using
* [Gradle](https://gradle.org/) as a build system,
* [Git](https://git-scm.com/) and [GitHub](https://github.com/FTSRG/theta) for version control,
* [GitHub actions](https://github.com/ftsrg/theta/actions) for continuous integration,
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

As the framework is under development, we suggest you to [sync your fork](https://help.github.com/articles/syncing-a-fork/) often and rebase your development branch(es) onto the master branch.

## Building

See [Build.md](Build.md).

## Developing in IntelliJ IDEA

- Theta can be imported into [IntelliJ IDEA](https://www.jetbrains.com/idea/) as an existing Gradle project by selecting the _build.gradle.kts_ file in the root of the repository.
- If you want to build the whole project (and not just run a single test for example), make sure to run the _build task of the whole project_. This can be done by opening the Gradle tab, and then selecting _theta / theta / Tasks / build / build_, right clicking and selecting _Run_.
- For code formatting and copyright header generation we use **spotless**.
    - Locally, formatting can be done manually by `gradlew spotlessApply`
    - Reformatting when saving a file can be set up by installing the `Spotless Applier` plugin (`Ctrl+Alt+s > Plugins`) and enabling it when saving (`Ctrl+Alt+s > Actions on Save`, enable `Run spotless`)
    - On Linux, the following pre-commit hook can be used to disable commits without formatting:
      ```
      #!/bin/bash
      
      # Run Spotless Check without interfering with uncommitted files
      ./gradlew spotlessCheck 2>/dev/null 1>&2
      
      # Capture the exit status of spotlessCheck
      SPOTLESS_STATUS=$?
      
      # If spotlessCheck fails, prevent the commit
      if [ $SPOTLESS_STATUS -ne 0 ]; then
        echo "Code format check failed. Please run './gradlew spotlessApply' to fix formatting issues."
        exit 1
      fi
      
      # If spotlessCheck passes, proceed with the commit
      echo "Spotless check passed."
      exit 0
      ```
      *(write the above into `.git/hooks/pre-commit` and enable execution rights on the file)*

## Coding conventions

See [Coding-conventions.md](Coding-conventions.md).
