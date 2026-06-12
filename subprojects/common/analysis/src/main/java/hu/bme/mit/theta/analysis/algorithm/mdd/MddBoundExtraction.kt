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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
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

  /** null result = the branch is known absent. */
  private val memo = HashMap<Pair<MddNode, MddNode?>, MddNode?>()

  /** The expression side's knowledge about an edge into the level below. */
  private sealed interface Sub

  /** Known absent. */
  private object Absent : Sub

  /** Unknown, permitted: the bound is the previous bound's remainder. */
  private object Unknown : Sub

  /** The expression tree continues at this handle (positioned at the consuming level). */
  private class At(val handle: MddHandle) : Sub

  /** Virtual level without constraint: every key maps to [sub] one more level down. */
  private class DefaultBelow(val sub: Sub) : Sub

  fun walkNode(e: MddHandle, p: MddHandle?): MddNode? {
    if (p != null && p.isTerminalZero) return null
    if (e.isTerminal) return if (e.isTerminalZero) null else one
    if (atCut(e.variableHandle)) return one
    val pEff = if (p != null && p.isTerminal) null else p

    val key = e.node to pEff?.node
    if (memo.containsKey(key)) return memo[key]

    val varHandle = e.variableHandle
    val result =
      if (e.isSkippedLevel) {
        val lowered = lowerOf(varHandle).getHandleFor(e.node)
        mergeLevel(emptyMap(), At(lowered), pEff, varHandle)
      } else
        when (val repr = e.node.representation) {
          is IdentityRepresentation -> {
            val cont = lowerOf(lowerOf(varHandle)).getHandleFor(repr.continuation)
            mergeLevel(emptyMap(), DefaultBelow(At(cont)), pEff, varHandle)
          }
          is MddExpressionRepresentation -> {
            val explicit = repr.explicitRepresentation
            val lower = lowerOf(varHandle)
            val eMap = LinkedHashMap<Int, Sub>()
            val cached = explicit.cacheView
            val cursor = cached.cursor()
            while (cursor.moveNext()) eMap[cursor.key()] = At(lower.getHandleFor(cursor.value()))
            // a default edge subsumes per-key knowledge
            if (cached.defaultValue() == null) {
              for (k in explicit.negativeKeys) eMap[k] = Absent
            }
            val eDefault =
              cached.defaultValue()?.let { At(lower.getHandleFor(it)) }
                ?: if (explicit.isComplete) Absent else Unknown
            mergeLevel(eMap, eDefault, pEff, varHandle)
          }
          else -> error("Unexpected representation in bound extraction: $repr")
        }
    memo[key] = result
    return result
  }

  /** Builds the bound node at [varHandle] from the expression side's edges and [p]'s. */
  private fun mergeLevel(
    eMap: Map<Int, Sub>,
    eDefault: Sub,
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

    val defaultNode = walkSub(eDefault, pDefault, lower)
    val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    if (defaultNode != null) builder.setDefault(defaultNode)
    var any = false
    for (k in keys) {
      val child = walkSub(eMap[k] ?: eDefault, pChildFor(k), lower)
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

  /** The bound below an edge with expression knowledge [sub] and bound remainder [pChild]. */
  private fun walkSub(sub: Sub, pChild: MddHandle?, varHandle: MddVariableHandle): MddNode? {
    if (sub == Absent) return null
    if (pChild != null && pChild.isTerminalZero) return null
    val pEff = if (pChild != null && pChild.isTerminal) null else pChild
    if (atCut(varHandle)) return one
    return when (sub) {
      Unknown -> materialize(pEff, varHandle)
      is At -> walkNode(sub.handle, pEff)
      is DefaultBelow -> mergeLevel(emptyMap(), sub.sub, pEff, varHandle)
      Absent -> error("unreachable")
    }
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
