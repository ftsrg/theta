plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-xta"))
    implementation(project(":theta-xta-analysis"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
}

application {
    mainClassName = "hu.bme.mit.theta.xta.cli.XtaCli"
}
