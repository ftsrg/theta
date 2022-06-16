plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-solver"))
    implementation("org.apache.commons:commons-compress:1.20")
    implementation("com.zaxxer:nuprocess:2.0.2")
    testImplementation(testFixtures(project(":theta-core")))
}
