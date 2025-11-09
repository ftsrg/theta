/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import org.gradle.api.tasks.SourceSetContainer
import org.gradle.api.tasks.testing.Test
import org.gradle.testing.jacoco.plugins.JacocoTaskExtension

plugins {
    base
    id("jacoco-common")
    id("io.freefair.aggregate-javadoc") version "5.2"
    id("io.codearte.nexus-staging") version "0.30.0" apply true
    id("org.sonarqube") version "4.2.1.3168"
    id("javasmt-common")
}

subprojects {
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
    version = "6.24.2"

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
    val jacocoRootReport by creating(JacocoReport::class) {
        group = "verification"
        description = "Generates merged code coverage report for all test tasks."

        reports {
            html.required.set(false)
            xml.required.set(true)
            csv.required.set(false)
        }

        // Collect all test tasks from all subprojects to gather execution data
        val allTestTasks = subprojects.flatMap { subproject ->
            subproject.tasks.withType<Test>()
        }

        // Depend on all test tasks to ensure they run before generating the report
        dependsOn(allTestTasks)

        // Collect all source directories from all subprojects
        val allSourceDirs = subprojects.flatMap { subproject ->
            subproject.extensions.findByType<SourceSetContainer>()
                ?.getByName("main")?.allSource?.srcDirs ?: emptySet()
        }

        // Collect all class directories from all subprojects
        val allClassDirs = subprojects.flatMap { subproject ->
            subproject.extensions.findByType<SourceSetContainer>()
                ?.getByName("main")?.output?.classesDirs?.files ?: emptySet()
        }

        // Collect all execution data files from all test tasks
        val allExecutionData = allTestTasks.map { task ->
            task.extensions.getByType<JacocoTaskExtension>().destinationFile
        }

        sourceDirectories.setFrom(files(allSourceDirs))
        classDirectories.setFrom(files(allClassDirs))
        executionData.setFrom(files(allExecutionData).filter { it?.exists() == true })
    }

    // Dummy test task for generating coverage report after ./gradlew test and ./gradlew check.
    val test by creating {
        finalizedBy(jacocoRootReport)
    }

    check {
        dependsOn(test)
    }

    project.tasks["sonar"].dependsOn(jacocoRootReport)

    nexusStaging {
        serverUrl = "https://s01.oss.sonatype.org/service/local/"
        username = System.getenv("OSSRH_USERNAME")
        password = System.getenv("OSSRH_PASSWORD")
    }
}
