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
    id("java-common")
    id("kotlin-common")
}

val noLogging = project.hasProperty("noLogging")

val loggerOutputDir = layout.buildDirectory.dir("generated/sources/logger/java/hu/bme/mit/theta/common/logging")

val generateLogger by tasks.registering(Copy::class) {
    val suffix = if (noLogging) "disabled" else "enabled"
    from(layout.projectDirectory.dir("src/main/templates/Logger.$suffix.kt"))
    into(loggerOutputDir)
    rename { "Logger.kt" }
}

sourceSets {
    main {
        java {
            srcDir(generateLogger.map { it.destinationDir })
        }
    }
}

tasks.named("compileKotlin") {
    dependsOn(generateLogger)
}

tasks.named("compileJava") {
    dependsOn(generateLogger)
}

dependencies {
    implementation(Deps.nuprocess)
    implementation(files(rootDir.resolve(Deps.delta)))
    implementation(Deps.fastutil)
}
