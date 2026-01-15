/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

plugins {
    base
    id("jacoco-common")
    id("io.freefair.aggregate-javadoc") version Versions.javadoc
    id("org.sonarqube") version Versions.sonarqube
    id("javasmt-common")
    id("release-info")
    id("docs-builder")
}

dependencies {
    rootProject.subprojects.forEach { subproject ->
        subproject.pluginManager.withPlugin("java") {
            javadoc(subproject)
        }
    }
}

subprojects {
    apply(plugin = "copyright-check")
    
    tasks.matching { it.name == "test" }.configureEach {
        dependsOn(rootProject.tasks.named("downloadJavaSmtLibs"))
    }
}

buildscript {
    val libPath: String by extra { rootProject.projectDir.resolve("lib").path }
    extra["execPath"] = "$libPath${File.pathSeparator}${System.getenv("PATH")}"
}

allprojects {
    group = "hu.bme.mit.theta"
    version = "6.27.16"

    apply(from = rootDir.resolve("gradle/shared-with-buildSrc/mirrors.gradle.kts"))
}

sonar {
    properties {
        property("sonar.projectKey", "ftsrg_theta")
        property("sonar.organization", "ftsrg-github")
        property("sonar.host.url", "https://sonarcloud.io")
        property(
            "sonar.coverage.jacoco.xmlReportPaths",
            "${project.layout.buildDirectory.asFile.get()}/reports/jacoco/jacocoRootReport/jacocoRootReport.xml"
        )
        property(
            "sonar.cpd.exclusions",
            "subprojects/xcfa/xcfa-cli/src/main/java/hu/bme/mit/theta/xcfa/cli/portfolio/**"
        )
    }
}

evaluationDependsOnChildren()

tasks {
    val jacocoRootReport by registering(JacocoReport::class) {
        group = "verification"
        description = "Generates merged code coverage report for all test tasks."

        reports {
            html.required.set(true)
            xml.required.set(true)
            csv.required.set(false)
        }

        val reportTasks = subprojects.mapNotNull { subproject ->
            subproject.tasks.findByName("jacocoTestReport")?.let { it as JacocoReport }
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
    val test by registering {
        finalizedBy(jacocoRootReport)
    }

    check {
        dependsOn(test)
    }

    project.tasks["sonar"].dependsOn(jacocoRootReport)
}
