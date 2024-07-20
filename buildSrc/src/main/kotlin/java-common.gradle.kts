/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
    java
    id("jacoco-common")
    id("maven-publish") // The correct plugin id for maven-related tasks
}

dependencies {
    val implementation: Configuration by configurations
    val testImplementation: Configuration by configurations
    val libPath: String by rootProject.extra

    implementation(Deps.Kotlin.stdlib)
    implementation(Deps.guava)
    implementation(Deps.gson)
    implementation(fileTree(mapOf("dir" to libPath, "include" to listOf("*.jar"))))
    implementation("org.fusesource.hawtjni:hawtjni-runtime:1.18")
    testImplementation(Deps.junit4)
    testImplementation(Deps.junit4engine)
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
        enableAssertions = true
    }

    named("jacocoTestReport") {
        dependsOn(named("test"))
    }

    withType<Test> {
        useJUnitPlatform()
    }

    withType<Test> {
        jvmArgs("-Xss5m", "-Xms512m", "-Xmx1g")
    }
}
