plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-cfa"))
    compile(project(":theta-solver-z3"))
    compile(project(":theta-c-frontend"))
    testCompile(project(":theta-c-frontend"))
}
