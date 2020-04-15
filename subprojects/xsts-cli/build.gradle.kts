plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-xsts"))
    compile(project(":theta-xsts-analysis"))
    compile(project(":theta-solver-z3"))
}

application {
    mainClassName = "hu.bme.mit.theta.xsts.cli.XstsCli"
}
