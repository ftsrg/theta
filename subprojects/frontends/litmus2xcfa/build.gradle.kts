plugins {
    id("java-common")
    id("antlr-grammar")
}
dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-xcfa"))
    testImplementation(project(":theta-xcfa-analysis"))
    testImplementation(project(":theta-cat"))
    testImplementation(project(":theta-analysis"))
    testImplementation(project(":theta-solver"))
    testImplementation(project(":theta-solver-z3"))
    testImplementation(project(":theta-litmus2xcfa"))
}