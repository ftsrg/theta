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
object Deps {
    val guava = "com.google.guava:guava:${Versions.guava}"

    object Antlr {
        val antlr = "org.antlr:antlr4:${Versions.antlr}"
        val runtime = "org.antlr:antlr4-runtime:${Versions.antlr}"
    }

    val z3 = "lib/com.microsoft.z3.jar"

    val jcommander = "com.beust:jcommander:${Versions.jcommander}"

    val junit4 = "junit:junit:${Versions.junit}"

    object Mockito {
        val core = "org.mockito:mockito-core:${Versions.mockito}"
    }
}
