plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-petrinet-model"))
    implementation(project(":theta-petrinet-analysis"))
    implementation(project(":theta-petrinet-xsts"))
    implementation(project(":theta-xsts"))
    implementation(project(":theta-xsts-analysis"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver"))
}

application {
    mainClassName = "hu.bme.mit.theta.xsts.cli.XstsCli"
}
