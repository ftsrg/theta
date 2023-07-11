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
    id("java-common")
    id("antlr-grammar")
    id("java-test-fixtures")
}

dependencies {
    implementation(project(":theta-common"))
    testFixturesImplementation(project(":theta-common"))
    val libPath: String by rootProject.extra
    testFixturesImplementation(fileTree(mapOf("dir" to libPath, "include" to listOf("*.jar"))))
    testFixturesImplementation(Deps.guava)
}
