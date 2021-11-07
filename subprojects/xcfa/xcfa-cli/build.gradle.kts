plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-xcfa"))
    compile(project(":theta-xcfa-analysis"))
    compile(project(":theta-solver-z3"))
    compile(project(":theta-cfa-analysis"))
    compile(project(":theta-cfa"))
    compile(project(":theta-cfa-cli"))
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.stateless.XcfaCli"
}
