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
    id("kotlin-common")
}

dependencies {
    testImplementation(project(":theta-common"))
    testImplementation(project(":theta-analysis"))
    testImplementation(project(":theta-core"))
    testImplementation(project(":theta-solver"))
    testImplementation(project(":theta-solver-z3-legacy"))
    testImplementation(project(":theta-cfa"))
    testImplementation(project(":theta-cfa-analysis"))
    testImplementation(project(":theta-xsts"))
    testImplementation(project(":theta-xsts-analysis"))
}
