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

import hu.bme.mit.delta.collections.IntObjMapView
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr

/**
 * [MddValuationCollector] restricted to the known part of a subtree: walks only the edges already
 * established by exploration (expression caches and explicit structural nodes), never calling
 * solvers. Identity and default levels carry no assignment, so the collected valuations may be
 * partial.
 */
object MddKnownValuationCollector {

  fun collect(handle: MddHandle): Set<Valuation> {
    val result = linkedSetOf<Valuation>()
    val assignments = ArrayDeque<Pair<Decl<*>, LitExpr<*>>>()

    fun walk(handle: MddHandle) {
      if (handle.isTerminal) {
        if (!handle.isTerminalZero) {
          val builder = ImmutableValuation.builder()
          assignments.forEach { (decl, value) -> builder.put(decl, value) }
          result.add(builder.build())
        }
        return
      }
      val lower = handle.variableHandle.lower.orElseThrow()
      if (handle.isSkippedLevel) {
        walk(lower.getHandleFor(handle.node))
        return
      }
      val repr = handle.node.representation
      if (repr is IdentityRepresentation) {
        walk(lower.lower.orElseThrow().getHandleFor(repr.continuation))
        return
      }
      // the edges exploration has already established, answered purely from the caches (expression
      // nodes) or the node itself (structural already explicit); never calls solvers
      val known: IntObjMapView<MddNode> =
        if (repr is MddExpressionRepresentation) repr.explicitRepresentation.cacheView
        else handle.node
      known.defaultValue()?.let { walk(lower.getHandleFor(it)) }
      val decl = handle.variableHandle.variable.orElseThrow().getTraceInfo(Decl::class.java)
      val cursor = known.cursor()
      while (cursor.moveNext()) {
        assignments.addLast(decl to LitExprConverter.toLitExpr(cursor.key(), decl.type))
        walk(lower.getHandleFor(cursor.value()))
        assignments.removeLast()
      }
    }

    walk(handle)
    return result
  }
}
