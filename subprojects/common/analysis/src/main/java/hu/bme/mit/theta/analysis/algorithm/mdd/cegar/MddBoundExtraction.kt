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

import hu.bme.mit.delta.java.mdd.BinaryOperationCache
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True

/**
 * Materializes the explored upper bound of [node] as a structural MDD over the abstract levels,
 * intersected in lockstep with the previous iteration's bound [prev]: cached edges recurse,
 * negatively cached keys are absent, a node the solver exhausted has no default edge (so its keys
 * are exhaustive even on unbounded domains), and unknown regions are permitted by a default edge.
 * Identity and skipped levels constrain nothing at their own level and widen to default edges; the
 * walk is cut at [dataBoundary], the topmost concrete witness level, below which saturation never
 * consults the relation. The lockstep intersection makes the bound accumulate across iterations
 * without composite views or delta set operations, and unknown regions reuse [prev]'s sub-MDDs.
 *
 * The result is level-dense: every level down to the cut carries a node (skipped levels are never
 * emitted), so consumers descend exactly one level per key. Where a default edge is present,
 * explicit edges to terminal zero record keys known absent.
 */
internal fun extractBound(node: MddHandle, prev: MddHandle?, dataBoundary: Any?): MddHandle {
  val extraction = BoundExtraction(node.variableHandle.mddGraph, dataBoundary)
  val result = extraction.walkNode(node, prev)
  return if (result == null) node.variableHandle.mddGraph.terminalZeroHandle
  else node.variableHandle.getHandleFor(result)
}

private class BoundExtraction(graph: MddGraph<*>, private val dataBoundary: Any?) {

  @Suppress("UNCHECKED_CAST")
  private val one: MddNode = (graph as MddGraph<Expr<*>>).getNodeFor(True())
  private val zero: MddNode = graph.terminalZeroNode
  private val zeroHandle: MddHandle = graph.terminalZeroHandle
  private val terminalVariableHandle = graph.terminalVariableHandle

  // walkNode is a binary operation over the expression node and the previous bound node (null when
  // there is no previous bound). An absent result (null) is memoized as the zero node, which the walk
  // never produces as a real result, so a cache hit is distinguishable from a miss.
  private val cache = BinaryOperationCache<MddNode, MddNode?, MddNode>()

  fun walkNode(e: MddHandle, p: MddHandle?): MddNode? {
    if (p != null && p.isTerminalZero) return null
    if (e.isTerminal) return if (e.isTerminalZero) null else one
    if (atCut(e.variableHandle)) return one
    val pEff = if (p != null && p.isTerminal) null else p

    val pNode = pEff?.node
    val cached = cache.getOrNull(e.node, pNode)
    if (cached != null) return if (cached === zero) null else cached

    val varHandle = e.variableHandle
    val lower = lowerOf(varHandle)
    val result =
      if (e.isSkippedLevel) {
        // a skipped level constrains nothing: widen to a default edge into the node one level down
        mergeLevel(emptyMap(), lower.getHandleFor(e.node), pEff, varHandle)
      } else
        when (val repr = e.node.representation) {
          is IdentityRepresentation -> {
            // identity spans the var and its primed copy, neither constrained: place the
            // continuation as a skipped level one down, so both levels widen to default edges
            mergeLevel(emptyMap(), lower.getHandleFor(repr.continuation), pEff, varHandle)
          }
          is MddExpressionRepresentation -> {
            val explored = repr.explored()
            val eMap = LinkedHashMap<Int, MddHandle?>()
            val cached = explored.knownEdges()
            val cursor = cached.cursor()
            while (cursor.moveNext()) eMap[cursor.key()] = lower.getHandleFor(cursor.value())
            // a default edge subsumes per-key knowledge
            if (cached.defaultValue() == null) {
              val absent = explored.knownAbsentKeys().cursor()
              while (absent.moveNext()) eMap[absent.elem()] = zeroHandle
            }
            val eDefault =
              cached.defaultValue()?.let { lower.getHandleFor(it) }
                ?: if (explored.isComplete) zeroHandle else null
            mergeLevel(eMap, eDefault, pEff, varHandle)
          }
          else -> error("Unexpected representation in bound extraction: $repr")
        }
    cache.addToCache(e.node, pNode, result ?: zero)
    return result
  }

  /**
   * Builds the bound node at [varHandle] from the expression side's edges and [p]'s. An edge target
   * (in [eMap] or [eDefault]) is null = unknown (permitted, falls back to [p]'s remainder), the
   * terminal zero handle = known absent, any other handle = the expression continues there.
   */
  private fun mergeLevel(
    eMap: Map<Int, MddHandle?>,
    eDefault: MddHandle?,
    p: MddHandle?,
    varHandle: MddVariableHandle,
  ): MddNode? {
    val lower = lowerOf(varHandle)
    val aligned = p != null && alignedAt(p, varHandle)

    val keys = LinkedHashSet(eMap.keys)
    if (aligned) {
      val cursor = p!!.node.cursor()
      while (cursor.moveNext()) keys.add(cursor.key())
    }

    val pDefault: MddHandle? =
      when {
        p == null -> null
        !aligned -> p
        else -> pHandleFor(p, p.node.defaultValue())
      }
    val pChildFor: (Int) -> MddHandle? = { key ->
      when {
        p == null -> null
        !aligned -> p
        else -> pHandleFor(p, p.node.get(key) ?: p.node.defaultValue())
      }
    }

    val defaultNode = walkEdge(eDefault, pDefault, lower)
    val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    if (defaultNode != null) builder.setDefault(defaultNode)
    var any = false
    for (k in keys) {
      val child = walkEdge(eMap.getOrDefault(k, eDefault), pChildFor(k), lower)
      if (child != null) {
        builder.set(k, child)
        any = true
      } else if (defaultNode != null) {
        // a key known absent under a permissive default
        builder.set(k, zero)
        any = true
      }
    }
    if (!any && defaultNode == null) return null
    return varHandle.checkInNode(MddStructuralTemplate.of(builder.buildAndReset())).node
  }

  /**
   * The bound below one edge. [target] is the expression side's continuation: null = unknown
   * (permitted, falls back to [pChild]'s remainder), the terminal zero handle = known absent, any
   * other handle = the expression continues there. [pChild] is the previous bound's remainder.
   */
  private fun walkEdge(
    target: MddHandle?,
    pChild: MddHandle?,
    varHandle: MddVariableHandle,
  ): MddNode? {
    if (target != null && target.isTerminalZero) return null
    if (pChild != null && pChild.isTerminalZero) return null
    val pEff = if (pChild != null && pChild.isTerminal) null else pChild
    if (atCut(varHandle)) return one
    return if (target == null) materialize(pEff, varHandle) else walkNode(target, pEff)
  }

  /** [p]'s remainder as a node at [varHandle], lifted through unconstrained levels. */
  private fun materialize(p: MddHandle?, varHandle: MddVariableHandle): MddNode {
    if (p == null) return one
    val wraps = mutableListOf<MddVariableHandle>()
    var vh = varHandle
    while (!alignedAt(p, vh)) {
      wraps.add(vh)
      vh = lowerOf(vh)
    }
    var node = p.node
    for (level in wraps.asReversed()) {
      val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
      builder.setDefault(node)
      node = level.checkInNode(MddStructuralTemplate.of(builder.buildAndReset())).node
    }
    return node
  }

  /**
   * The child of aligned bound node [p] as a handle. A missing child means absent (the terminal
   * zero handle), never unconstrained: an aligned bound constrains every key.
   */
  private fun pHandleFor(p: MddHandle, child: MddNode?): MddHandle {
    if (child == null || child == zero) return zeroHandle
    return lowerOf(p.variableHandle).getHandleFor(child)
  }

  private fun alignedAt(p: MddHandle, varHandle: MddVariableHandle): Boolean =
    p.variableHandle.variable.map { it.traceInfo }.orElse(null) ==
      varHandle.variable.map { it.traceInfo }.orElse(null)

  private fun atCut(varHandle: MddVariableHandle): Boolean =
    dataBoundary != null && varHandle.variable.map { it.traceInfo }.orElse(null) == dataBoundary

  private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
    if (varHandle.lower.isPresent) varHandle.lower.get() else terminalVariableHandle
}
