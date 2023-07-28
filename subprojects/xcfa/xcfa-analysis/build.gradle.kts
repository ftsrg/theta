plugins {
    id("kotlin-common")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-c-frontend"))
    testImplementation(project(":theta-c2xcfa"))
    testImplementation(project(":theta-solver-z3"))
    testImplementation(project(":theta-solver"))
}
