plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-cfa"))
}

application {
    mainClassName = "hu.bme.mit.theta.cfa.metrics.CfaMetrics"
}
