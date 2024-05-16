plugins {
    id("java-common")
}

dependencies {
    implementation(project(":theta-analysis"))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-xta"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-solver-z3"))
    testImplementation(project(":theta-solver-z3"))
    testImplementation(project(":theta-solver"))
    implementation(project(":theta-solver-smtlib"))

}
