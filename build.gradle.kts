import org.sonarqube.gradle.SonarQubeTask

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
    // DO NOT MODIFY THIS BY HAND!!! Use the bumpVersion task!
    version = /*<THETA_VERSION>*/ "4.0.0" /*</THETA_VERSION>*/

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
    apply(plugin = "jacoco-common")
}

sonarqube {
    properties {
        property("sonar.projectKey", "ftsrg_theta")
        property("sonar.organization", "ftsrg-github")
        property("sonar.host.url", "https://sonarcloud.io")
        property("sonar.coverage.jacoco.xmlReportPaths", "build/reports/jacoco/jacocoRootReport/jacocoRootReport.xml,build/reports/jacoco/test/jacocoTestReport.xml")
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

    named<SonarQubeTask>("sonarqube") {
        dependsOn(jacocoRootReport)
    }

    val bumpVersion by creating {
        fun generateVersion(version: String): String {
            val updateMode = project.properties["mode"] ?: "patch"
            val (oldMajor, oldMinor, oldPatch) = version.split(".").map(String::toInt)
            var (newMajor, newMinor, newPatch) = arrayOf(oldMajor, oldMinor, 0)
            when (updateMode) {
                "major" -> newMajor = (oldMajor + 1).also { newMinor = 0 }
                "minor" -> newMinor = oldMinor + 1
                /* "patch" */ else -> newPatch = oldPatch + 1
            }
            return "$newMajor.$newMinor.$newPatch"
        }

        doLast {
            if(!project.hasProperty("mode") && !project.hasProperty("overrideVersion")) {
                println("""
                    Usage:
                    ./gradlew bumpVersion [-P[mode=major|minor|patch]|[overrideVersion=x]]
                """.trimIndent())
                return@doLast
            }

            val oldVersion = rootProject.version as String
            val newVersion = project.properties["overrideVersion"] as String? ?: generateVersion(oldVersion)
            println("Bump version from $oldVersion to $newVersion")

            var script = buildFile.readText()
            script = script.replace(
                """/*<THETA_VERSION>*/ "$oldVersion" /*</THETA_VERSION>*/""",
                """/*<THETA_VERSION>*/ "$newVersion" /*</THETA_VERSION>*/"""
            )
            buildFile.writeText(script)
        }
    }
}

subprojects {
    tasks.named("jacocoTestReport", JacocoReport::class) {
        dependsOn("test")
        reports {
            html.required.set(false)
            xml.required.set(true)
            csv.required.set(false)
        }
    }

    tasks.named("test") {
        finalizedBy("jacocoTestReport")
    }
}