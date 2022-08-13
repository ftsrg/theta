plugins {
    id("kotlin-common")
    id("antlr-grammar")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
}

tasks.named("compileKotlin") {
    dependsOn("generateGrammarSource")
}
tasks.named("compileTestKotlin") {
    dependsOn("generateTestGrammarSource")
}
