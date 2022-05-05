plugins {
    id("java-common")
}

dependencies {
    implementation(files(rootDir.resolve(Deps.delta)))
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-solver"))
    testImplementation(project(":theta-solver-z3"))
}
