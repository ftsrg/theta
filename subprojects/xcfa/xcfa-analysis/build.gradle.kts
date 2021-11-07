plugins {
    id("java-common")
}

dependencies {
    compile(project(":theta-cfa-analysis"))
    compile(project(":theta-xcfa"))
    compile(project(":theta-core"))
    compile(project(":theta-cat"))
    compile(project(":theta-common"))
    compile(project(":theta-solver-smtlib"))
}
