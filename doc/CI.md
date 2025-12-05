# CI/CD techniques in Theta

As Theta is a complex project with many developers and users, it needs to have certain standards for collaboration, code style and user-facing stability. This document details the CI/CD features and how-to steps of Theta.

## Collaboration standards

The `master` branch is protected, meaning direct pushes to the branch are forbidden. Every modification is handled via _Pull Requests (PRs)_. For a PR to be mergable, the following criteria need to be fulfilled:

* At least one reviewer accepted the PR (no self-reviews are allowed)
* All conversations are marked _resolved_
* The source is up-to-date with the destination
* All automated checks pass

### Automated Checks

The following GitHub Actions workflows run automatically on all PRs and pushes:

#### Code Quality and Style

| Workflow | Purpose | Location |
|----------|---------|----------|
| **check-copyright** | Verifies all source files have the Apache 2.0 license header from `doc/copyright-header.txt` | [check-copyright.yml](https://github.com/ftsrg/theta/blob/master/.github/workflows/check-copyright.yml) |
| **check-formatting** | Ensures code follows the Google style guide (configured in `.idea/codeStyles/Project.xml`) using Spotless | [check-formatting.yml](https://github.com/ftsrg/theta/blob/master/.github/workflows/check-formatting.yml) |
| **sonar** | Runs SonarCloud analysis for code quality, requiring minimum 60% test coverage on new code | [sonar.yml](https://github.com/ftsrg/theta/blob/master/.github/workflows/sonar.yml) |
| **check-version** | Ensures the version in `build.gradle.kts` differs from the master branch version | [check-version.yml](https://github.com/ftsrg/theta/blob/master/.github/workflows/check-version.yml) |

#### Platform-Specific Builds and Tests

| Workflow | Purpose | Platforms |
|----------|---------|-----------|
| **linux-build-test-deploy** | Primary CI/CD workflow: builds, runs unit tests, generates archives, creates binaries, and manages deployments | Ubuntu 24.04 |
| **win-build-test** | Ensures code builds and tests pass on Windows | Windows latest |
| **mac-build-test** | Ensures code builds and tests pass on macOS | macOS 15 |

### Automated Actions on PR Failures

When a check fails, the following workflows automatically comment on the PR to guide developers:

- **Copyright failure**: Instructs to run `./gradlew applyCopyright`
- **Formatting failure**: Instructs to run `./gradlew spotlessApply`

## Code Style

Theta adopts the [Google Java style guide](https://github.com/google/styleguide/blob/gh-pages/intellij-java-google-style.xml) with small adjustments, configured in `.idea/codeStyles/Project.xml`.

### Formatting

Use `./gradlew spotlessApply` to automatically format all code locally. The [check-formatting.yml](https://github.com/ftsrg/theta/blob/master/.github/workflows/check-formatting.yml) workflow verifies this in CI.

### Copyright Headers

Every source code file must include the license header from `doc/copyright-header.txt`. Apply headers locally with:
```bash
./gradlew applyCopyright
```

### Code Quality Analysis

Theta uses [SonarCloud](https://sonarcloud.io/) for static analysis, with quality gates enforcing:
- Minimum 60% test coverage on new code
- Code smells and security issue limits
- No critical issues in new code

Rules and gates may change based on feedback.

## CI/CD Workflows in Detail

### linux-build-test-deploy.yml

The primary CI/CD workflow orchestrates the entire build, test, and deployment pipeline.

**On every push and PR:**
1. **build** job: Compiles the project (no tests) using Java 21
   - Uploads JARs as artifacts (`ThetaJars`)
   - Creates badges for build status

2. **test-linux** job: Runs all unit tests on Ubuntu 24.04
   - Depends on: build
   - Creates status badges

3. **javadoc** job: Generates aggregate Javadoc documentation
   - Publishes to GitHub Pages on `workflow_dispatch` with release message on master

**On integration test runs (benchexec):**
4. **create-archives** job: Builds tool distributions for each configured variant
   - Tasks defined in matrix: `buildArchiveTheta-svcomp`, `buildArchiveEmergenTheta-svcomp`, etc.
   - Outputs ZIP files as artifacts

5. **test-benchexec** job: Runs integration tests using BenchExec
   - Tests multiple tool/config combinations (software, CHC, hardware, PetriNet, PLC, Statechart)
   - Depends on: create-archives
   - Executes benchmarks against integration test suites

6. **collect-results** job: Aggregates and reports BenchExec results
   - Depends on: test-benchexec

**On `workflow_dispatch` with master branch and release message:**
7. **deploy-release** job: Creates GitHub release with JARs
   - Depends on: test-linux, create-archives

8. **deploy-maven** job: Publishes to Maven Central
   - Requires: `OSSRH_USERNAME`, `OSSRH_PASSWORD`, `OSSRH_TOKEN_USERNAME`, `OSSRH_TOKEN_PASSWORD`, `PGP_KEY`, `PGP_PWD`

9. **test-docker** job: Builds and tests Docker images (dry-run by default)
   - Projects: theta-cfa-cli, theta-sts-cli, theta-xsts-cli, theta-xta-cli, theta-xcfa-cli

10. **deploy-docker** job: Publishes Docker images to DockerHub and GitHub Container Registry
    - Only runs on `workflow_dispatch` with release message on master
    - Requires: `DOCKER_USERNAME`, `DOCKER_TOKEN`

11. **deploy-zenodo** job: Archives releases to Zenodo
    - Only runs on `workflow_dispatch` with release message on master
    - Requires: `zenodo_token`
    - Tools: Theta-svcomp, EmergenTheta-svcomp, Thorn-svcomp, Theta-chccomp

12. **deploy-docs** job: Publishes documentation to GitHub Pages
    - Builds wiki with MkDocs
    - Only deploys on `workflow_dispatch` with release message on master

### Other Workflows

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| **cleanup-workflows** | Manual or scheduled | Removes old workflow run artifacts |
| **reformat-code** | Manual dispatch | Formats code and creates PR with changes |
| **apply-copyright** | Manual dispatch | Applies copyright headers and creates PR with changes |
| **version-bump** | Manual dispatch | Automatically increments version |

## Integration Tests

Integration tests use [BenchExec](https://github.com/sosy-lab/benchexec) for standardized tool evaluation. Test suites are defined in `integration-tests/` with corresponding tool configurations.

### Test Categories

- **software** (`integration-tests/software/`): SV-COMP benchmarks (reachability, termination)
- **chc** (`integration-tests/chc/`): CHC-COMP benchmarks
- **hardware** (`integration-tests/hardware/`): HWMCC benchmarks
- **petrinet** (`integration-tests/petrinet/`): Petri net model checking
- **plc** (`integration-tests/plc/`): PLC verification benchmarks
- **statechart** (`integration-tests/statechart/`): Statechart verification benchmarks

### Adding New Integration Tests

To add new integration tests to the CI pipeline, follow these steps:

#### 1. Create Integration Test Configuration

Create a BenchExec XML configuration in `integration-tests/<category>/theta.xml` with the following structure:

```xml
<?xml version="1.0"?>
<!DOCTYPE benchmark PUBLIC "+//IDN sosy-lab.org//DTD BenchExec benchmark 1.9//EN" "https://www.sosy-lab.org/benchexec/benchmark-2.3.dtd">
<benchmark tool="theta" timelimit="60 s" hardtimelimit="90 s">

<!-- config -->

  <rundefinition name="Theta-<category>-Integration-Test">
    <tasks name="<task-name>">
      <propertyfile>properties/<property-file>.prp</propertyfile>
      <include><category>/<benchmark-subset>.yml</include>
      <!-- Add more includes for test cases -->
    </tasks>
    <!-- Add more task definitions if needed -->
  </rundefinition>
</benchmark>
```

**Key elements:**
- `tool`: Should be "theta"
- `timelimit`: Per-run timeout (typically 60s for benchmarks)
- `hardtimelimit`: Hard timeout before forceful termination (typically 90s)
- `<tasks name>`: Logical grouping of test cases
- `<propertyfile>`: Property file specifying verification goal (e.g., `unreach-call.prp`)
- `<include>`: YAML-formatted benchmark case definition
- `<!-- config -->`: Will be replaced by CLI options

#### 2. Add Test Case Files

Store benchmark cases as YAML files in `integration-tests/<category>/<subset>/` (e.g., `svcomp25/aim-100-1-6-sat-1.c.yml`). Each YAML file must specify:

```yaml
programs:
  - file: <path-to-input-file>
    # Optional: language, main function, etc.
options:
  # Tool-specific options
```

#### 3. Update linux-build-test-deploy.yml Workflow

Add a matrix entry to the `test-benchexec` job to include your new test configuration:

```yaml
test-benchexec:
  strategy:
    matrix:
      include:
        # ... existing entries ...
        - tool: Theta-<tool-name>
          config: "--specific --flags --for --test"
          name: <Category>_<TestName>
          input_type: <category>  # Must match your integration-tests/<category> folder
```

**Parameters:**
- `tool`: Tool variant to test (must match a packaged archive name)
- `config`: Command-line flags for the tool
- `name`: Human-readable test name (used in reports)
- `input_type`: Directory under `integration-tests/` containing the test suite

## Packaged Tool Variants

Tool variants are binary distributions with pre-configured solvers and execution environments. They are created via the `archive-packaging` Gradle plugin.

### Adding a New Tool Variant

To create a new packaged variant (e.g., a new XCFA tool configuration):

#### 1. Configure Archive Packaging in build.gradle.kts

In the CLI subproject's `build.gradle.kts` (e.g., `subprojects/xcfa/xcfa-cli/build.gradle.kts`), add to the `archivePackaging` block:

```kotlin
archivePackaging {
    variant {
        toolName = "Theta-custom"           // Unique tool identifier
        inputFlags = "--custom --flags"     // Command-line flags 
        solvers = listOf(                   // Optional: SMT solvers to bundle
            "cvc5:1.2.0",
            "mathsat:5.6.12"
        )
        includeSolverCli = true             // Include solver installation utility
        scriptName = "theta-start.sh"       // Script from scripts/ directory
        readmeTemplate = file("src/main/resources/archive-packaging/README-CUSTOM.md")  // Optional
        smoketestSource = file("src/main/resources/archive-packaging/smoketest.sh")     // Optional
        inputSource = file("src/main/resources/archive-packaging/input.c")              // Optional
    }
}
```

**Configuration options:**
- `toolName`: Archive and Gradle task identifier (becomes `buildArchive<toolName>`)
- `inputFlags`: Default command-line arguments
- `solvers`: List of SMT solver versions to install (format: `solver:version`)
- `includeSolverCli`: Include solver management JAR (default: true)
- `scriptName`: Entry point script from `scripts/` (default: `theta-start.sh`)
- `readmeTemplate`: Custom README template (optional, variables: `TOOL_NAME`, `TOOL_VERSION`, `INPUT_FLAG`, `CONTENTS`)
- `smoketestSource`: Executable smoke test script (optional)
- `inputSource`: Sample input file for smoke test (optional)

#### 2. Create Supporting Files (Optional)

Create in `src/main/resources/archive-packaging/`:

- **README-CUSTOM.md**: Custom README with placeholders
  ```markdown
  # TOOL_NAME v TOOL_VERSION
  
  Default command: `./theta-start.sh INPUT_FLAG <input-file>`
  
  CONTENTS
  ```

- **smoketest.sh**: Executable test script
  ```bash
  #!/bin/bash
  ./theta-start.sh TOOL_NAME_PLACEHOLDER <input> --expected-result RESULT
  ```

- **input.c**: Sample input file

#### 3. Update the Workflow

Add an entry to the `create-archives` matrix in `linux-build-test-deploy.yml`:

```yaml
create-archives:
  strategy:
    matrix:
      include:
        # ... existing entries ...
        - toolName: Theta-custom
          gradleTask: buildArchiveTheta-custom
```

#### 4. (Optional) Add Integration Tests

If testing the new variant, add to `test-benchexec` matrix in `linux-build-test-deploy.yml`:

```yaml
test-benchexec:
  strategy:
    matrix:
      include:
        # ... existing entries ...
        - tool: Theta-custom
          config: "--custom --flags"
          name: Custom_TestName
          input_type: <category>
```

### Packaged Variant Artifacts

The `archive-packaging` plugin generates ZIP archives containing:

- `theta.jar`: Main executable JAR
- `theta-smtlib.jar`: Solver installation utility (if includeSolverCli=true)
- `solvers/`: Installed SMT solver binaries
- `theta-start.sh`: Entry point script
- `README.md`: Tool documentation
- `GENERAL_README.md`: Theta project README
- `LIB_LICENSES.md`: Third-party library licenses
- `LICENSE`: Apache 2.0 license
- `CONTRIBUTORS.md`: Project contributors
- `lib/`: Native libraries (OpenSSL, etc.)
- `smoketest.sh`: Optional smoke test (if configured)
- `input.c`: Optional sample input (if configured)

Archives are built by tasks like `./gradlew buildArchive<ToolName>` and uploaded as GitHub artifacts for download and distribution.

## Deployments

For stable releases, binaries are deployed to multiple distribution channels:

### Deployment Triggers

Deployments occur only when `linux-build-test-deploy.yml` is manually triggered via `workflow_dispatch` with:
- A release message (required)
- Target: master branch

### Deployment Targets

| Target | Format | Details |
|--------|--------|---------|
| **GitHub Releases** | JAR files, archives | Created via `create-release` action |
| **Maven Central** | JAR, source, Javadoc | Published via `publish` Gradle task |
| **DockerHub** | Docker images | Pushed for each CLI tool (`ftsrg/theta-*-cli`) |
| **GitHub Container Registry** | Docker images | Pushed for each CLI tool (`ftsrg/theta-*-cli`) |
| **Zenodo** | Archives | Versioned snapshots for competition tools (Theta-svcomp, EmergenTheta-svcomp, Thorn-svcomp, Theta-chccomp) |
| **GitHub Pages** | Wiki, Javadoc | Published to `gh-pages` branch under `/wiki` and `/javadoc` |

### Deployment Actions

- `create-release`: Creates GitHub release and publishes JARs
- `zenodo-release`: Archives tool variants to Zenodo
- `docker-deploy`: Builds and pushes Docker images
- `docker-login`: Authenticates to DockerHub and GHCR
