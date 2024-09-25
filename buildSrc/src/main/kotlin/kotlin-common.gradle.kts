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
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

apply(plugin = "java-common")
plugins {
    kotlin("jvm")
}
dependencies {
    val implementation: Configuration by configurations
    implementation(Deps.Kotlin.stdlib)
    implementation(Deps.Kotlin.reflect)
    implementation(Deps.Mockito.kotlin)
}
tasks {
    withType<KotlinCompile>() {
        kotlinOptions {
            jvmTarget = "17"
            freeCompilerArgs = listOf("-Xjvm-default=all-compatibility")
        }
    }
}

// Check if "antlr-common" plugin is applied and if the "generateGrammarSource" task is available
// If yes, add a task dependency from "compileKotlin" to "generateGrammarSource"
project.plugins.withType<AntlrPlugin> {
    val generateGrammarTask = tasks.findByName("generateGrammarSource")
    if (generateGrammarTask != null) {
        project.tasks.named("compileKotlin").configure {
            dependsOn(generateGrammarTask)
        }
    }
    val generateTestGrammarTask = tasks.findByName("generateTestGrammarSource")
    if (generateTestGrammarTask != null) {
        project.tasks.named("compileTestKotlin").configure {
            dependsOn(generateTestGrammarTask)
        }
    }
}