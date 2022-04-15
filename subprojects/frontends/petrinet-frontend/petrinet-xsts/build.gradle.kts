plugins {
    id("java-common")
}

dependencies {
    compile(project(":theta-core"))
    compile(project(":theta-xsts"))
    compile(project(":theta-petrinet-model"))

    testImplementation(project(":theta-xsts-analysis"))
    testImplementation(project(":theta-solver-z3"))
}