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

import org.gradle.internal.os.OperatingSystem

plugins {
    id("java-common")
    id("kotlin-common")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-xcfa"))
}

tasks.test {
    if (OperatingSystem.current().isLinux) {
        val nativeLibTasks = project(":theta-llvm").tasks
        val task = nativeLibTasks.withType(LinkSharedLibrary::class)
        if (task.any { !it.enabled }) {
            enabled = false
        }
        val linkTask = task.first()
        dependsOn(linkTask)
        systemProperty(
            "java.library.path",
            linkTask.linkedFile.get().asFile.parent + ":/usr/java/packages/lib/amd64:/usr/lib64:/lib64:/lib:/usr/lib",
        )
    }
}
