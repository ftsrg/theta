plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-sts"))
    compile(project(":theta-sts-analysis"))
    compile(project(":theta-solver-z3"))
}

application {
    mainClassName = "hu.bme.mit.theta.sts.cli.StsCli"
}
