/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
    id("kotlin-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-chc-frontend"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-c2xcfa"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-grammar"))
    implementation(project(":theta-llvm2xcfa"))
    implementation("com.zaxxer:nuprocess:2.0.5")
    runtimeOnly("org.jetbrains.kotlin:kotlin-scripting-jsr223:1.7.10")
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.XcfaCli"
}

//tasks.test {
//    if (OperatingSystem.current().isLinux) {
//        val nativeLibTasks = project(":theta-llvm").tasks
//        dependsOn(nativeLibTasks.build)
//
//        val linkTask = nativeLibTasks.withType(LinkSharedLibrary::class).first()
//        val existingLibraryPath = systemProperties["java.library.path"]
//        val newLibraryPath = "${existingLibraryPath}:${linkTask.linkedFile.get().asFile.parent}"
//        systemProperty("java.library.path", newLibraryPath)
//    }
//}

