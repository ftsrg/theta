plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    compile(project(":theta-petrinet-frontend"))

    compile(project(":theta-common"))
    compile(project(":theta-core"))
}
