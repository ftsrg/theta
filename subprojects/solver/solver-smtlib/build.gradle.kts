plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-solver"))
    compile("org.apache.commons:commons-compress:1.20")
    compile("com.zaxxer:nuprocess:2.0.2")
    testImplementation(testFixtures(project(":theta-core")))
}
