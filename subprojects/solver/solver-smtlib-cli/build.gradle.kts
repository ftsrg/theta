plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-common"))
    implementation(project(":theta-solver"))
}

application {
    mainClassName = "hu.bme.mit.theta.solver.smtlib.cli.SmtLibCli"
}
