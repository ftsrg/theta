rootProject.name = "theta"

include(
    "common/analysis",
    "common/common",
    "common/core",
    "common/grammar",

    "frontends/c-frontend",
    "frontends/chc-frontend",

    "cfa/cfa",
    "cfa/cfa-analysis",
    "cfa/cfa-cli",

    "sts/sts",
    "sts/sts-analysis",
    "sts/sts-cli",

    "xcfa/xcfa",
    "xcfa/cat",
    "xcfa/c2xcfa",
    "xcfa/litmus2xcfa",
    "xcfa/xcfa-analysis",
    "xcfa/xcfa-cli",
    "xcfa/litmus-cli",

    "xta/xta",
    "xta/xta-analysis",
    "xta/xta-cli",

    "xsts/xsts",
    "xsts/xsts-analysis",
    "xsts/xsts-cli",

    "solver/solver",
    "solver/solver-z3",
    "solver/solver-smtlib",
    "solver/solver-smtlib-cli"
)

for (project in rootProject.children) {
    val projectPath = project.name
    val projectName = projectPath.split("/").last()
    project.projectDir = file("subprojects/$projectPath")
    project.name = "${rootProject.name}-$projectName"
}