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
package hu.bme.mit.theta.xcfa.analysis.monolithic

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.EliminateSelfLoops
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

/**
 * Block encoding for [XcfaSingleThreadToMonolithicAdapter]: a transition is a whole loop-free path
 * between the locations that full LBE keeps (loop heads, branch points it cannot merge, init,
 * error), so a bound counts blocks instead of edges. A k-induction step then starts at a block
 * boundary, not in the middle of a loop body. Only for error-location reachability: edges that
 * cannot reach the error location are dropped first.
 *
 * LBE merges branches into NondetLabels, and their SMT encoding does not tell which branch a model
 * took. So, before LBE, each branching location stores the index of its taken outgoing edge in a
 * ghost variable, and [expand] follows these choices through the graph recorded before LBE.
 */
internal class BlockEncoding(parseContext: ParseContext) {

  private val intType: Type = ctrlType(parseContext)

  private class Recorded(
    val outgoing: Map<String, List<XcfaEdge>>,
    val choices: Map<String, VarDecl<*>>,
  )

  private val recorded = LinkedHashMap<String, Recorded>()
  private var choiceCnt = 0

  val passes: List<ProcedurePass> =
    listOf(
      EliminateSelfLoops(),
      ErrorReachingEdgesPass(),
      RecordChoicesPass(),
      LbePass(parseContext, LbePass.LbeLevel.LBE_FULL),
    )

  fun isChoiceVar(v: VarDecl<*>): Boolean = v.name.startsWith(CHOICE_PREFIX)

  /** The original labels of [blockEdge] along the path the choices in [post] select. */
  fun expand(procedure: String, blockEdge: XcfaEdge, post: Valuation): XcfaLabel {
    val graph = recorded[procedure] ?: error("No recorded graph for procedure $procedure")
    val values = post.toMap().mapKeys { it.key.name }
    val labels = mutableListOf<XcfaLabel>()
    var metadata: MetaData = EmptyMetaData
    var current = blockEdge.source.name
    var steps = 0
    do {
      val out = graph.outgoing[current] ?: error("Location $current was not recorded")
      val next =
        if (out.size == 1) out.single()
        else {
          val choice = graph.choices.getValue(current)
          val value = values[choice.name] as? LitExpr<*> ?: error("No value for ${choice.name}")
          out[value.value]
        }
      labels.add(next.label)
      metadata = metadata.combine(next.metadata)
      current = next.target.name
      check(++steps <= graph.outgoing.size) {
        "No block path ${blockEdge.source} -> ${blockEdge.target}"
      }
    } while (current != blockEdge.target.name)
    return SequenceLabel(
      labels.flatMap { if (it is SequenceLabel) it.labels else listOf(it) },
      metadata,
    )
  }

  /** Keeps only the edges from which the error location is reachable. */
  private class ErrorReachingEdgesPass : ProcedurePass {
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
      val error = builder.errorLoc.orElse(null) ?: return builder
      val keep = HashSet<XcfaEdge>()
      val worklist = ArrayDeque(error.incomingEdges)
      while (worklist.isNotEmpty()) {
        val edge = worklist.removeFirst()
        if (keep.add(edge)) worklist.addAll(edge.source.incomingEdges)
      }
      builder.getEdges().filter { it !in keep }.forEach(builder::removeEdge)
      return builder
    }
  }

  private inner class RecordChoicesPass : ProcedurePass {
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
      val outgoing = LinkedHashMap<String, List<XcfaEdge>>()
      val choices = LinkedHashMap<String, VarDecl<*>>()
      for (loc in builder.getLocs().toList()) {
        val out = loc.outgoingEdges.toList()
        outgoing[loc.name] = out
        if (out.size <= 1) continue
        val choice = Decls.Var(CHOICE_PREFIX + choiceCnt++, intType)
        choices[loc.name] = choice
        builder.addVar(choice)
        out.forEachIndexed { index, edge ->
          val mark = AssignStmtLabel(choice, ctrlLit(intType, index))
          val labels =
            if (edge.label is SequenceLabel) (edge.label as SequenceLabel).labels
            else listOf(edge.label)
          builder.removeEdge(edge)
          builder.addEdge(edge.withLabel(SequenceLabel(listOf(mark) + labels, edge.label.metadata)))
        }
      }
      recorded[builder.name] = Recorded(outgoing, choices)
      return builder
    }
  }

  companion object {
    const val CHOICE_PREFIX = "__theta_block_choice_"
  }
}
