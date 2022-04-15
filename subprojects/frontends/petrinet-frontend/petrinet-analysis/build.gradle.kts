plugins {
    id("java-common")
}

dependencies {
    implementation(Deps.logback)
    implementation(Deps.axiomApi)
    implementation(Deps.axiomImpl)
    implementation(Deps.jing)

    compile(project(":theta-core"))
    compile(project(":theta-analysis"))
    compile(project(":theta-petrinet-model"))
}