plugins {
    id("java-common")
    id("antlr-grammar")
}

tasks.withType<Test> {
    this.testLogging {
        this.showStandardStreams = true
    }
}

dependencies {
    compile(project(":theta-common"))
}
