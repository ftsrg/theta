plugins {
    id("java-common")
    id("antlr-grammar")
    id("java-test-fixtures")
}

dependencies {
    compile(project(":theta-common"))
    val libPath: String by rootProject.extra
    testFixturesImplementation(fileTree(mapOf("dir" to libPath, "include" to listOf("*.jar"))))
}
