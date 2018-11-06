plugins {
    base
}

allprojects {
    group = "hu.bme.mit.inf.theta"
    version = "0.0.1-SNAPSHOT"

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
}

val libPath: String by extra { rootProject.rootDir.resolve("lib").path }
val execPath by extra { "$libPath${File.pathSeparator}${System.getenv("PATH")}" }
