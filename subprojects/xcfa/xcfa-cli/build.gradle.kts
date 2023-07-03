plugins {
    id("java-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-cfa-analysis"))
    implementation(project(":theta-cfa"))
    implementation(project(":theta-common"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-chc-frontend"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-cfa-cli"))
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.XcfaCli"
}
