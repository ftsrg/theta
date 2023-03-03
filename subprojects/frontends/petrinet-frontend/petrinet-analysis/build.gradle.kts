plugins {
    id("java-common")
}

dependencies {
    implementation(Deps.logback)
    implementation(Deps.axiomApi)
    implementation(Deps.axiomImpl)
    implementation(Deps.jing)

    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-petrinet-model"))
}