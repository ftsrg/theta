plugins {
    id("java-common")
    id("antlr-grammar")
}

dependencies {
    implementation(project(":theta-cfa"))
    implementation(project(":theta-cfa-analysis"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-core"))
    implementation(project(":theta-cat"))
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-solver-smtlib"))
}
