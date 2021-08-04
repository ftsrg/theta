plugins {
    id("java-common")
}

dependencies {
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-solver"))
    implementation(files(rootDir.resolve(Deps.z3)))
    testImplementation(testFixtures(project(":theta-core")))
}
