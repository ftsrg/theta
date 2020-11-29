plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    compile(project(":theta-xcfa"))
    compile(project(":theta-xcfa-analysis"))
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.XcfaCli"
}
