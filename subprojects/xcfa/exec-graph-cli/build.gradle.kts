plugins {
    id("java-common")
    id("antlr-grammar")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-cat"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-graph-solver"))
}


application {
    mainClassName = "hu.bme.mit.theta.xcfa.execgraph.cli.ExecutionGraphCli"
}
