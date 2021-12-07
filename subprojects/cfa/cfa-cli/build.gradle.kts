plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-cfa"))
    compile(project(":theta-cfa-analysis"))
    compile(project(":theta-solver-z3"))
}

application {
    mainClassName = "hu.bme.mit.theta.cfa.cli.CfaCli"
}
