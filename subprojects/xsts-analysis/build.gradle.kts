plugins {
    id("java-common")
}

//tasks.withType<Test> {
//    this.testLogging {
//        this.showStandardStreams = true
//    }
//}

dependencies {
    compile(project(":theta-analysis"))
    compile(project(":theta-common"))
    compile(project(":theta-core"))
    compile(project(":theta-xsts"))
    testImplementation(project(":theta-solver-z3"))
}
