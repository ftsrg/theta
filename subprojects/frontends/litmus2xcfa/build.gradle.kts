plugins {
    id("java-common")
    id("antlr-grammar")
}
dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-xcfa"))
}