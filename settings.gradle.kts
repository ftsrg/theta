rootProject.name = "theta"

include(
        "analysis",
        "cfa",
        "cfa2dot",
        "cfa-analysis",
        "cfa-cli",
        "cfa-metrics",
        "common",
        "core",
        "solver",
        "solver-z3",
        "sts",
        "sts-analysis",
        "sts-cli",
        "xta",
        "xta-analysis",
        "xta-cli",
        "xsts"
)

for (project in rootProject.children) {
    val projectName = project.name
    project.projectDir = file("subprojects/$projectName")
    project.name = "${rootProject.name}-$projectName"
}
