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
    id("kotlin-common")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-graph-solver"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-xcfa-dss-decomposition"))
    implementation(project(":theta-solver"))

    testImplementation(project(":theta-grammar"))
    testImplementation(project(":theta-solver-z3"))
    // Only tests need a real checker to exercise runWorkerConfig against - production code takes
    // one as an injected factory instead (see WorkerConfigDelegator.kt), specifically so this
    // module does not depend on xcfa-cli: xcfa-cli depends on DSS for --algorithm DSS, and this
    // module depending back on xcfa-cli would have made that a circular project dependency.
    testImplementation(project(":theta-xcfa-cli"))
}
