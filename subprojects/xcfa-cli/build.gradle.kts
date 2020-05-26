plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-xcfa"))
    compile(project(":theta-xcfa-analysis-alt"))
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.XcfaCli"
}
