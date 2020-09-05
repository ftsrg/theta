plugins {
    id("java-common")
}

dependencies {
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-analysis"))
    compile(project(":theta-cfa"))
    compile(project(":theta-xcfa"))
}
