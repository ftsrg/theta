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

import hu.bme.mit.delta.java.mdd.JavaMddFactory
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
 * Materializes [node]'s cached-as-present edges as a structural over-approximation over the abstract
 * levels. The present cache is exhaustive: an uncached key is pruned (no default edge), sound because
 * GSAT probes every transition of every reachable source, so an unprobed key is unsatisfiable. Only
 * the last iteration's node is read — its constrained exploration already excludes what earlier
 * iterations pruned.
 *
 * The bound is built under [boundTop], a mirror order on a fresh graph: checking the structural nodes
 * into the source order would collide them with its procedural expression nodes and force
 * solver-driven equality enumeration. [node] is descended through its own handle while [boundTop]
 * advances in lockstep. Identity and skipped levels widen to default edges; the walk is cut at
 * [dataBoundary], the topmost concrete witness level, below which saturation never consults the bound.
 */
internal fun extractBound(
  node: MddHandle,
  boundTop: MddVariableHandle,
  dataBoundary: Any?,
): MddHandle {
  val result = BoundExtraction(boundTop.mddGraph, dataBoundary).walkNode(node, boundTop)
  return if (result == null) boundTop.mddGraph.terminalZeroHandle else boundTop.getHandleFor(result)
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
    val result =
      if (e.isSkippedLevel) {
        // a skipped level constrains nothing: widen to a default edge into the node one level down
        level(emptyMap(), walkNode(srcLower.getHandleFor(e.node), tgtLower), target)
      } else
        when (val repr = e.node.representation) {
          is IdentityRepresentation ->
            // identity spans the var and its primed copy, neither constrained: widen to default edges
            level(emptyMap(), walkNode(srcLower.getHandleFor(repr.continuation), tgtLower), target)
          is MddExpressionRepresentation -> {
            val known = repr.explored().knownEdges()
            val edges = LinkedHashMap<Int, MddNode>()
            val cursor = known.cursor()
            while (cursor.moveNext()) {
              walkNode(srcLower.getHandleFor(cursor.value()), tgtLower)?.let {
                edges[cursor.key()] = it
              }
            }
            // a present default edge (skip / ofDefault) is kept; without one, an uncached key is
            // pruned (no default), making the present cache exhaustive
            val default =
              known.defaultValue()?.let { walkNode(srcLower.getHandleFor(it), tgtLower) }
            level(edges, default, target)
          }
          else -> error("Unexpected representation in bound extraction: $repr")
        }
    cache.addToCache(e.node, result ?: zero)
    return result
  }

  /** The bound node at [target]; null when it has neither an edge nor a default (fully absent). */
  private fun level(
    edges: Map<Int, MddNode>,
    default: MddNode?,
    target: MddVariableHandle,
  ): MddNode? {
    if (edges.isEmpty() && default == null) return null
    val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    if (default != null) builder.setDefault(default)
    edges.forEach { (key, child) -> builder.set(key, child) }
    return target.checkInNode(MddStructuralTemplate.of(builder.buildAndReset())).node
  }

  private fun atCut(varHandle: MddVariableHandle): Boolean =
    dataBoundary != null && varHandle.variable.map { it.traceInfo }.orElse(null) == dataBoundary

  private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
    if (varHandle.lower.isPresent) varHandle.lower.get()
    else varHandle.mddGraph.terminalVariableHandle
}
