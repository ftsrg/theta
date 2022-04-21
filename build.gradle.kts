plugins {
    base
    id("jacoco-common")
    id("io.freefair.aggregate-javadoc") version "5.2"
    id("org.sonarqube") version "3.3"
}

buildscript {
    val libPath: String by extra { rootProject.projectDir.resolve("lib").path }
    extra["execPath"] = "$libPath${File.pathSeparator}${System.getenv("PATH")}"
}

allprojects {
    group = "hu.bme.mit.inf.theta"
    version = "4.0.0"

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
}

sonarqube {
    properties {
        property("sonar.projectKey", "ftsrg_theta")
        property("sonar.organization", "ftsrg-github")
        property("sonar.host.url", "https://sonarcloud.io")
        property("sonar.coverage.jacoco.xmlReportPaths", "build/reports/jacoco/test/jacocoTestReport.xml")
    }
}

evaluationDependsOnChildren()

tasks {
    val jacocoRootReport by creating(JacocoReport::class) {
        group = "verification"
        description = "Generates merged code coverage report for all test tasks."

        reports {
            html.required.set(true)
            xml.required.set(true)
            csv.required.set(false)
        }

        val reportTasks = subprojects.mapNotNull { subproject ->
            subproject.tasks.named("jacocoTestReport", JacocoReport::class).orNull
        }

        dependsOn(reportTasks.flatMap { it.dependsOn })

        sourceDirectories.setFrom(files(reportTasks.map { it.allSourceDirs }))
        classDirectories.setFrom(files(reportTasks.map { it.allClassDirs }))
        val allExecutionData = files(reportTasks.map { it.executionData })
        // We only set executionData for declaring dependencies during task graph construction,
        // subprojects without tests will be filtered out in doFirst.
        executionData.setFrom(allExecutionData.filter { it.exists() })
    }

    // Dummy test task for generating coverage report after ./gradlew test and ./gradlew check.
    val test by creating {
        finalizedBy(jacocoRootReport)
    }

    check {
        dependsOn(test)
    }
}

subprojects {
    tasks.named("jacocoTestReport", JacocoReport::class) {
        reports {
            html.required.set(false)
            xml.required.set(true)
            csv.required.set(false)
        }
    }
}