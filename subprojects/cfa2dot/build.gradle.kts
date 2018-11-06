plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-cfa-analysis"))
}

application {
    mainClassName = "hu.bme.mit.theta.cfa.cfa2dot.CfaToDotMain"
}
