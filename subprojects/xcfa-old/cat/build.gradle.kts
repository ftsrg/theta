plugins {
    id("java-common")
    id("antlr-grammar")
    id("jacoco-common")
}

dependencies {
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-common"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-core"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-solver-z3"))
}
