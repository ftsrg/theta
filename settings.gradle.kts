rootProject.name = "theta"

include(
        "analysis",
        "cfa",
        "cfa-analysis",
        "cfa-cli",
        "common",
        "core",
        "solver",
        "solver-z3",
        "sts",
        "sts-analysis",
        "sts-cli",
        "xcfa",
        "xcfa-cli",
        "xcfa-analysis",
        "xta",
        "xta-analysis",
        "xta-cli"
)

for (project in rootProject.children) {
    val projectName = project.name
    project.projectDir = file("subprojects/$projectName")
    project.name = "${rootProject.name}-$projectName"
}
