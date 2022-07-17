plugins {
    id("java-common")
}

dependencies {
    implementation(project(":theta-analysis"))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-xsts"))
    testImplementation(project(":theta-solver-z3"))
}
