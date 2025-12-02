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

sealed class Statement

data class IfStatement(
    val options: PromelaOptions,
    val sequence: List<Statement>
) : Statement()

data class DoStatement(
    val options: PromelaOptions,
    val sequence: List<Statement>
) : Statement()

data class ForStatement(
    val range: Range,
    val sequence: List<Statement>
) : Statement()

data class AtomicStatement(
    val sequence: List<Statement>
) : Statement()

data class DStepStatement(
    val sequence: List<Statement>
) : Statement()

data class SelectStatement(
    val range: Range
) : Statement()

data class Sequence(
    val steps: List<Statement>
)

data class Range(
    val name: String,
    val start: String,
    val end: String
)

data class PromelaOptions(
    val sequences: List<Sequence>
)
