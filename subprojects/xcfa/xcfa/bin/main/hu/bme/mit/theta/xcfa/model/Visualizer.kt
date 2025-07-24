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
package hu.bme.mit.theta.xcfa.model

typealias LabelCustomizer = (XcfaEdge) -> String

fun XCFA.toDot(edgeLabelCustomizer: LabelCustomizer? = null): String =
  xcfaToDot(name, procedures.map { DottableProcedure(it) }, edgeLabelCustomizer)

fun XcfaProcedure.toDot(edgeLabelCustomizer: LabelCustomizer? = null): String =
  xcfaProcedureToDot(name, locs, edges, edgeLabelCustomizer)

@Suppress("unused")
fun XcfaBuilder.toDot(edgeLabelCustomizer: LabelCustomizer? = null): String =
  xcfaToDot(name, getProcedures().map { DottableProcedure(it) }, edgeLabelCustomizer)

fun XcfaProcedureBuilder.toDot(edgeLabelCustomizer: LabelCustomizer? = null): String =
  xcfaProcedureToDot(name, getLocs(), getEdges(), edgeLabelCustomizer)

private class DottableProcedure(
  private val procedure: XcfaProcedure?,
  private val procedureBuilder: XcfaProcedureBuilder?,
) {
  constructor(procedure: XcfaProcedure) : this(procedure, null)

  constructor(procedureBuilder: XcfaProcedureBuilder) : this(null, procedureBuilder)

  fun toDot(edgeLabelCustomizer: LabelCustomizer? = null): String =
    procedure?.toDot(edgeLabelCustomizer) ?: procedureBuilder!!.toDot(edgeLabelCustomizer)
}

private fun xcfaToDot(
  name: String,
  procedures: List<DottableProcedure>,
  edgeLabelCustomizer: LabelCustomizer? = null,
): String {
  val builder = StringBuilder()
  builder.appendLine("digraph G {")
  builder.appendLine("label=\"$name\";")

  for ((i, procedure) in procedures.withIndex()) {
    builder.appendLine("subgraph cluster_$i {")
    builder.appendLine(procedure.toDot(edgeLabelCustomizer))
    builder.appendLine("}")
  }

  builder.appendLine("}")
  return builder.toString()
}

private fun xcfaProcedureToDot(
  name: String,
  locs: Set<XcfaLocation>,
  edges: Set<XcfaEdge>,
  edgeLabelCustomizer: LabelCustomizer? = null,
): String {
  val builder = StringBuilder()
  builder.appendLine("label=\"$name\";")
  locs.forEach { builder.appendLine("${it.name}[];") }
  edges.forEach {
    builder.appendLine(
      "${it.source.name} -> ${it.target.name} [label=\"${it.label} ${edgeLabelCustomizer?.invoke(it) ?: ""}\"];"
    )
  }
  return builder.toString()
}
