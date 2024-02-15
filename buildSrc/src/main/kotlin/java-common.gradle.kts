apply<JavaPlugin>()
apply(plugin = "jacoco-common")

dependencies {
    val implementation: Configuration by configurations
    val testImplementation: Configuration by configurations
    val libPath: String by rootProject.extra

    implementation(Deps.guava)
    implementation(fileTree(mapOf("dir" to libPath, "include" to listOf("*.jar"))))
    implementation("org.fusesource.hawtjni:hawtjni-runtime:1.18")
    testImplementation(Deps.junit4)
    testImplementation(Deps.Mockito.core)
}

tasks {
    withType<JavaCompile>() {
        sourceCompatibility = Versions.java
        targetCompatibility = Versions.java
    }

    val libPath: String by rootProject.extra
    val execPath: String by rootProject.extra

    withType<Test>() {
        environment["PATH"] = execPath
        environment["LD_LIBRARY_PATH"] = libPath
        enableAssertions = true
    }

    withType<JavaExec>() {
        environment["PATH"] = execPath
        environment["LD_LIBRARY_PATH"] = libPath
        enableAssertions = false
    }

    named("jacocoTestReport") {
        dependsOn(named("test"))
    }
}
