plugins {
    id("java-common")
}

dependencies {
    compile(project(":theta-xcfa"))
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-solver"))
    compile(project(":theta-solver-z3"))
}
