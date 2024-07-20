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
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-petrinet-model"))
    implementation(project(":theta-petrinet-analysis"))
    implementation(project(":theta-petrinet-xsts"))
    implementation(project(":theta-xsts"))
    implementation(project(":theta-xsts-analysis"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-core"))
    implementation(project(":theta-common"))
    implementation(project(":theta-solver-z3-legacy"))
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-solver"))
}

application {
    mainClass.set("hu.bme.mit.theta.xsts.cli.XstsCli")
}
