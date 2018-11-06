apply<JavaPlugin>()
apply<JacocoPlugin>()

dependencies {
    val implementation: Configuration by configurations
    val testImplementation: Configuration by configurations

    implementation(Deps.guava)
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
    }
}

extensions.configure<JacocoPluginExtension> {
    toolVersion = Versions.jacoco
}
