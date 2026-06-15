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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.UnaryOperationCache
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityTemplate

object MddExplicitRepresentationExtractor {

  /**
   * Builds a variable order mirroring [top]'s chain on a fresh graph. Extracting through it keeps
   * the explicit nodes out of the source order's unique tables, where hash collisions with the
   * procedural expression nodes force solver-driven equality enumeration.
   */
  fun mirrorTopOf(top: MddVariableHandle): MddVariableHandle {
    val mirrorOrder =
      JavaMddFactory.getDefault().createMddVariableOrder(ExprLatticeDefinition.forExpr())
    generateSequence(top) { it.lower.orElse(null) }
      .mapNotNull { it.variable.orElse(null) }
      .toList()
      .asReversed()
      .forEach { mirrorOrder.createOnTop(MddVariableDescriptor.copy(it)) }
    return mirrorOrder.defaultSetSignature.topVariableHandle
  }

  fun transform(node: MddHandle, variable: MddVariableHandle): MddHandle =
    transform(node, variable, UnaryOperationCache())

  fun transform(
    node: MddHandle,
    variable: MddVariableHandle,
    cache: UnaryOperationCache<MddHandle, MddHandle>,
  ): MddHandle {
    val cached = cache.getOrNull(node)
    if (cached != null) {
      return cached
    }

    // node is descended through its own variableHandle; variable is only the check-in
    // target and may belong to a different order mirroring the source levels
    val result: MddHandle
    if (node.isTerminal) {
      if (node.isTerminalZero) {
        result = variable.mddGraph.terminalZeroHandle
      } else {
        val mddGraph: MddGraph<Any> = variable.mddGraph as MddGraph<Any>
        result = mddGraph.terminalVariableHandle.getHandleFor(mddGraph.getNodeFor(node.data))
      }
    } else {
      if (node.node.representation is IdentityRepresentation) {
        val s =
          transform(
            node.variableHandle.lower
              .get()
              .lower
              .get()
              .getHandleFor((node.node.representation as IdentityRepresentation).continuation),
            variable.lower.get().lower.orElse(null),
            cache,
          )
        result =
          if (!s.isTerminalZero) {
            variable.checkInNode(IdentityTemplate(s.node))
          } else {
            variable.mddGraph.terminalZeroHandle
          }
      } else {
        val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
        Preconditions.checkArgument(node.node.representation is MddExpressionRepresentation)
        val expressionRepresentation = node.node.representation as MddExpressionRepresentation
        val explicitRepresentation = expressionRepresentation.explicitRepresentation

        if (explicitRepresentation.cacheView.defaultValue() != null) {
          val s =
            transform(
              node.variableHandle.lower
                .get()
                .getHandleFor(explicitRepresentation.cacheView.defaultValue()),
              variable.lower.orElse(null),
              cache,
            )
          if (!s.isTerminalZero) templateBuilder.setDefault(s.node)
        } else {
          val cursor = explicitRepresentation.cacheView.cursor()
          while (cursor.moveNext()) {
            val s =
              transform(
                node.variableHandle.lower.get().getHandleFor(cursor.value()),
                variable.lower.orElse(null),
                cache,
              )
            if (!s.isTerminalZero) templateBuilder.set(cursor.key(), s.node)
          }
        }

        result = variable.checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset()))
      }
    }
    cache.addToCache(node, result)
    return result
  }
}
