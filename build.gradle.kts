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
    version = "2.2.0"

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
}

evaluationDependsOnChildren()

tasks {
    val jacocoRootReport by creating(JacocoReport::class) {
        group = "verification"
        description = "Generates merged code coverage report for all test tasks."

        reports {
            html.isEnabled = false
            xml.isEnabled = true
            csv.isEnabled = false
        }

        val reportTasks = subprojects.mapNotNull { subproject ->
            subproject.tasks.named("jacocoTestReport", JacocoReport::class).orNull
        }

        dependsOn(reportTasks.flatMap { it.dependsOn })

        sourceDirectories = files(reportTasks.map { it.allSourceDirs })
        classDirectories = files(reportTasks.map { it.allClassDirs })
        val allExecutionData = files(reportTasks.map { it.executionData })
        // We only set executionData for declaring dependencies during task graph construction,
        // subprojects without tests will be filtered out in doFirst.
        executionData = allExecutionData

        doFirst {
            executionData = allExecutionData.filter { it.exists() }
        }
    }

    // Dummy test task for generating coverage report after ./gradlew test and ./gradlew check.
    val test by creating {
        finalizedBy(jacocoRootReport)
    }

    check {
        dependsOn(test)
    }
}
