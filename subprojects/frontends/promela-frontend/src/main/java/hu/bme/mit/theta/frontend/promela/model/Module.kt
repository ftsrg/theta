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
package hu.bme.mit.theta.frontend.promela.model

sealed class Module {
}

data class Proctype(
    val active: String?,
    val name: String,
    val declList: DeclList?,
    val priority: String?,
    val enabler: String?,
    val sequence: List<Statement>
) : Module()

data class Init(
    val priority: String?,
    val sequence: List<Statement>
) : Module()

data class Never(
    val sequence: List<Statement>
) : Module()

data class Trace(
    val sequence: List<Statement>
) : Module()

data class Utype(
    val name: String,
    val declList: DeclList
) : Module()

data class Mtype(
    val names: List<String>
) : Module()