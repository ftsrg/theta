plugins {
    base
    id("jacoco-common")
}

buildscript {
    val libPath: String by extra { rootProject.projectDir.resolve("lib").path }
    extra["execPath"] = "$libPath${File.pathSeparator}${System.getenv("PATH")}"
}

allprojects {
    group = "hu.bme.mit.inf.theta"
    version = "0.0.1-SNAPSHOT"

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
}

evaluationDependsOnChildren()

val jacocoRootReport by tasks.creating(JacocoReport::class) {
    reports {
        html.isEnabled = false
        xml.isEnabled = true
        csv.isEnabled = false
    }

    val reportTasks = subprojects.mapNotNull { subproject ->
        subproject.tasks.named("jacocoTestReport", JacocoReport::class).orNull
    }
    sourceDirectories = files(reportTasks.map { it.allSourceDirs })
    classDirectories = files(reportTasks.map { it.allClassDirs })
    val allExecutionData = files(reportTasks.map { it.executionData })
    // We only declare dependencies, subprojects without tests will be filtered out in doFirst.
    executionData = allExecutionData

    doFirst {
        executionData = allExecutionData.filter { it.exists() }
    }
}
