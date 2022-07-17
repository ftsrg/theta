plugins {
    id("java-common")
}

dependencies {
    implementation(project(":theta-analysis"))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-sts"))
    implementation(project(":theta-solver"))
    testImplementation(project(":theta-solver-z3"))
}
