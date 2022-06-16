plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    compile(project(":theta-xcfa"))
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-solver"))
    compile(project(":theta-solver-z3"))
}
