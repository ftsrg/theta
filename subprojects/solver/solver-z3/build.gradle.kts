plugins {
    id("java-common")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-solver"))
    implementation(files(rootDir.resolve(Deps.z3)))
    testImplementation(testFixtures(project(":theta-core")))
}
