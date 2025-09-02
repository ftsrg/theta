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
plugins {
    id("java-common")
    id("antlr-grammar")
    id("java-test-fixtures")
    id("kotlin-common")
    id("kaml-serialization")
    id("kotlinx-serialization")
    id("com.google.devtools.ksp") version "1.9.25-1.0.20"
}

dependencies {
    implementation(project(":theta-common"))
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.6.3")
    testFixturesImplementation(project(":theta-common"))
    val libPath: String by rootProject.extra
    testFixturesImplementation(fileTree(mapOf("dir" to libPath, "include" to listOf("*.jar"))))
    testFixturesImplementation(Deps.guava)
    ksp(project(":theta-ksp-processor"))
}

kotlin {
    sourceSets["main"].kotlin.srcDir("build/generated/ksp/main/kotlin")
}

tasks.withType<com.google.devtools.ksp.gradle.KspTaskJvm> {
    when (name) {
        "kspKotlin" -> dependsOn("generateGrammarSource")
        "kspTestKotlin" -> dependsOn("generateTestGrammarSource")
        "kspTestFixturesKotlin" -> dependsOn("generateTestFixturesGrammarSource")
    }
}

ksp {
    arg("incremental", "false")
}
