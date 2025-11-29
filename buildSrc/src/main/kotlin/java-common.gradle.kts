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

import org.gradle.api.plugins.JavaPlugin
import org.gradle.api.tasks.SourceSetContainer
import org.gradle.testing.jacoco.tasks.JacocoReport

plugins {
    java
    id("jacoco-common")
    id("maven-artifact")
    id("com.diffplug.spotless")
}

dependencies {
    val implementation: Configuration by configurations
    val testImplementation: Configuration by configurations

    implementation(Deps.Kotlin.stdlib)
    implementation(Deps.guava)
    implementation(Deps.gson)
    implementation(files(*(Deps.mpfr_java.map(rootDir::resolve).toTypedArray())))

    testImplementation(Deps.junit5)
    testImplementation(Deps.junit5param)
    testImplementation(Deps.junit5engine)
    testImplementation(Deps.Mockito.core)
    testImplementation(Deps.Mockito.extension)
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
        environment["DYLD_LIBRARY_PATH"] = libPath
        systemProperty("java.library.path", libPath)
        enableAssertions = true
    }

    named<JacocoReport>("jacocoTestReport") {
        dependsOn(named("test"))
        
        // Include source and class directories from all subprojects to capture cross-project coverage
        // Exclude generated sources (build/generated-src) and generated packages with .dsl.gen suffix
        rootProject.subprojects.forEach { subproject ->
            subproject.plugins.withType<JavaPlugin> {
                val sourceSets = subproject.extensions.getByType<SourceSetContainer>()
                additionalSourceDirs.from(sourceSets.getByName("main").allSource.srcDirs.filter {
                    !it.path.contains("build/generated-src")
                })
                additionalClassDirs.from(files(sourceSets.getByName("main").output).asFileTree.matching {
                    exclude("**/dsl/gen/**")
                })
            }
        }
        
        // Also exclude from the main source and class directories
        sourceDirectories.setFrom(files(sourceDirectories.files.filter {
            !it.path.contains("build/generated-src")
        }))
        classDirectories.setFrom(files(classDirectories.files.map {
            fileTree(it) {
                exclude("**/dsl/gen/**")
            }
        }))
    }

    withType<Test> {
        useJUnitPlatform()
    }

    withType<Test> {
        jvmArgs("-Xss5m", "-Xms512m", "-Xmx1g")
    }
}

spotless {
    ratchetFrom("origin/master")

    isEnforceCheck = false
    
    val year = "\$YEAR" // you can't escape $ in raw strings..
    val licenseHeader = """            /*
             *  Copyright $year Budapest University of Technology and Economics
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
             */""".trimIndent()


    java {
        importOrder("java|javax", "hu.bme.", "")
        removeUnusedImports()
        googleJavaFormat("1.24.0").aosp().reflowLongStrings()
        formatAnnotations()

        licenseHeader(licenseHeader)
    }
    kotlin {
        ktfmt("0.51").googleStyle()

        licenseHeader(licenseHeader)
    }
    kotlinGradle {
        target("*.gradle.kts") // default target for kotlinGradle

        ktlint()
    }
}