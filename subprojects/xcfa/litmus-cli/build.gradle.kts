plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-litmus2xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-cat"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver-smtlib"))
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.litmus.cli.LitmusCli"
}
