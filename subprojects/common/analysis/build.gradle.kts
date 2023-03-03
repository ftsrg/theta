plugins {
    id("java-common")
}

dependencies {
    implementation(files(rootDir.resolve(Deps.delta)))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-solver"))
    testImplementation(project(":theta-solver-z3"))
}
