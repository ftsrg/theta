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
package hu.bme.mit.theta.xcfa.dss.decomposition

fun BlockGraph.toDot(): String {
  val sb = StringBuilder()
  sb.append("digraph BlockGraph {\n")
  sb.append("  rankdir=LR;\n")
  sb.append("  node [shape=box, fontname=\"monospace\"];\n")
  for (block in blocks.sortedBy { it.id }) {
    sb.append("  \"${dotEscape(block.id)}\" [label=\"${nodeLabel(block)}\"")
    val style = nodeStyle(block)
    if (style.isNotEmpty()) {
      sb.append(", ").append(style)
    }
    sb.append("];\n")
  }
  for (block in blocks.sortedBy { it.id }) {
    for (successorId in block.successorIds.sorted()) {
      sb.append("  \"${dotEscape(block.id)}\" -> \"${dotEscape(successorId)}\";\n")
    }
  }
  sb.append("}\n")
  return sb.toString()
}

private fun nodeLabel(block: Block): String {
  val lines = buildList {
    add(block.id)
    add("${block.initialLocation.name} -> ${block.finalLocation.name}")
  }
  return lines.joinToString("\\n") { dotEscape(it) }
}

private fun nodeStyle(block: Block): String = if (block.isRoot) "peripheries=2" else ""

private fun dotEscape(s: String): String = s.replace("\\", "\\\\").replace("\"", "\\\"")
