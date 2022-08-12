plugins {
    id("kotlin-common")
    id("antlr-grammar")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
}

tasks.named("compileKotlin") {
    dependsOn("generateGrammarSource")
}
