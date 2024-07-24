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
import com.github.jengelman.gradle.plugins.shadow.ShadowPlugin
import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar

apply<ApplicationPlugin>()
apply<ShadowPlugin>()

tasks {
    val libPath: String by rootProject.extra
    val execPath: String by rootProject.extra

    fun JavaExec.setupEnvironment() {
        environment["PATH"] = execPath
        environment["LD_LIBRARY_PATH"] = libPath
    }

    named("run", JavaExec::class).configure { setupEnvironment() }
    named("runShadow", JavaExec::class).configure { setupEnvironment() }
}

tasks.withType<ShadowJar>() {
    manifest {
        attributes["Implementation-Version"] = archiveVersion
    }
    isZip64 = true
}
