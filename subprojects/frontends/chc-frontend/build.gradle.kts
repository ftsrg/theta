plugins {
    id("java-common")
    id("antlr-grammar")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-solver-smtlib"))
}

application {
    mainClass.set("hu.bme.mit.theta.frontend.chc.Main")
}