plugins {
    id("java-common")
}

dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-xsts"))
    implementation(project(":theta-petrinet-model"))

    testImplementation(project(":theta-xsts-analysis"))
    testImplementation(project(":theta-solver-z3"))
    testImplementation(project(":theta-solver"))
    testImplementation(project(":theta-analysis"))
}