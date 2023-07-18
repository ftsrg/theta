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

package hu.bme.mit.theta.xcfa.model

fun XCFA.toDot(): String {
    val builder = StringBuilder()
    builder.appendLine("digraph G {")
    builder.appendLine("label=\"$name\";")

    var i = 0
    for (procedure in procedures) {
        builder.appendLine("subgraph cluster_" + i++ + " {")
        builder.appendLine(procedure.toDot())
        builder.appendLine("}")
    }

    builder.appendLine("}")
    return builder.toString()
}

fun XcfaProcedure.toDot(): String {
    val builder = StringBuilder()
    builder.appendLine("label=\"$name\";")
    locs.forEach { builder.appendLine(it.name + "[];") }
    edges.forEach {
        builder.appendLine(
            it.source.name + " -> " + it.target.name + "[label=\"" + it.label.toString() + "\"];")
    }
    return builder.toString()
}