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
package hu.bme.mit.theta.analysis.algorithm.mdd.cegar

import hu.bme.mit.delta.collections.IntObjMapView
import hu.bme.mit.delta.collections.impl.IntObjMapViews
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.UnaryOperationCache
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True

/**
 * Materializes [sourceHandle]'s cached-as-present edges as a structural over-approximation over the abstract
 * levels. The present cache is exhaustive: an uncached key is pruned (no default edge), sound because
 * GSAT probes every transition of every reachable source, so an unprobed key is unsatisfiable. Only
 * the last iteration's node is read — its constrained exploration already excludes what earlier
 * iterations pruned.
 *
 * The bound is built under [targetVariable], a mirror order on a fresh graph: checking the structural nodes
 * into the source order would collide them with its procedural expression nodes and force
 * solver-driven equality enumeration. [sourceHandle] is descended through its own handle while [targetVariable]
 * advances in lockstep. Identity and skipped levels widen to default edges; the walk is cut at
 * [dataBoundary], the topmost concrete witness level, below which saturation never consults the bound.
 */
internal fun extractBound(
  sourceHandle: MddHandle,
  targetVariable: MddVariableHandle,
  dataBoundary: Any?,
): MddHandle {
  val result = BoundExtraction(targetVariable.mddGraph, dataBoundary).walkNode(sourceHandle, targetVariable)
  return if (result == null) targetVariable.mddGraph.terminalZeroHandle else targetVariable.getHandleFor(result)
}

private class BoundExtraction(graph: MddGraph<*>, private val dataBoundary: Any?) {

  @Suppress("UNCHECKED_CAST")
  private val one: MddNode = (graph as MddGraph<Expr<*>>).getNodeFor(True())
  private val zero: MddNode = graph.terminalZeroNode

  // walkNode is a unary operation over the expression node. An absent result (null) is memoized as
  // the zero node, which the walk never produces as a real result, so a hit is distinguishable.
  private val cache = UnaryOperationCache<MddNode, MddNode>()

  /**
   * [e] is read through its own (source) handle; [target] is the mirror handle the bound node is
   * checked into, advanced one level per recursion in lockstep with [e].
   */
  fun walkNode(e: MddHandle, target: MddVariableHandle): MddNode? {
    if (e.isTerminal) return if (e.isTerminalZero) null else one
    if (atCut(e.variableHandle)) return one

    val cached = cache.getOrNull(e.node)
    if (cached != null) return if (cached === zero) null else cached

    val srcLower = lowerOf(e.variableHandle)
    val tgtLower = lowerOf(target)
    val template =
      if (e.isSkippedLevel) {
        // a skipped level constrains nothing: widen to a default edge one level down
        MddStructuralTemplate.of(
          IntObjMapView.empty(walkNode(srcLower.getHandleFor(e.node), tgtLower))
        )
      } else
        when (val repr = e.node.representation) {
          is IdentityRepresentation ->
            // identity spans the var and its primed copy, neither constrained: widen to a default edge
            MddStructuralTemplate.of(
              IntObjMapView.empty(walkNode(srcLower.getHandleFor(repr.continuation), tgtLower))
            )
          is MddExpressionRepresentation ->
            // edges + default never coexist, so one transform handles both: a present default widens,
            // while a key whose child prunes to null is dropped, making the present cache exhaustive
            MddStructuralTemplate.of(
              IntObjMapViews.Transforming(repr.explored().knownEdges()) { child ->
                child?.let { walkNode(srcLower.getHandleFor(it), tgtLower) }
              }
            )
          else -> error("Unexpected representation in bound extraction: $repr")
        }
    // an empty template canonizes to the terminal zero node; map it back to the absent (null) result
    val node = target.checkInNode(template).node
    val result = if (node === zero) null else node
    cache.addToCache(e.node, result ?: zero)
    return result
  }

  private fun atCut(varHandle: MddVariableHandle): Boolean =
    dataBoundary != null && varHandle.variable.map { it.traceInfo }.orElse(null) == dataBoundary

  private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
    if (varHandle.lower.isPresent) varHandle.lower.get()
    else varHandle.mddGraph.terminalVariableHandle
}
