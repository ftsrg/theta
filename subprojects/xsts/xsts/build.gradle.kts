plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    compile(project(":theta-pnml-frontend"))

    compile(project(":theta-common"))
    compile(project(":theta-core"))
}
