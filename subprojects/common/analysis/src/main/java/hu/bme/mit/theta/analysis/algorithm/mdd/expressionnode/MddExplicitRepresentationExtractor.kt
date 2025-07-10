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
package hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.UnaryOperationCache
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityTemplate

object MddExplicitRepresentationExtractor {

  val structToSym: MutableMap<MddHandle, MddHandle> = mutableMapOf()

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
        val identityNode = variable.checkInNode(
          IdentityTemplate(
            transform(
              variable.lower.get().lower.get().getHandleFor((node.node.representation as IdentityRepresentation).continuation),
              variable.lower.get().lower.orElse(null),
              cache
            ).node
          )
        )
        result = identityNode
      } else {
        val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
        Preconditions.checkArgument(node.node.representation is MddExpressionRepresentation)
        val expressionRepresentation = node.node.representation as MddExpressionRepresentation
        val explicitRepresentation = expressionRepresentation.explicitRepresentation

        if (explicitRepresentation.cacheView.defaultValue() != null) {
          templateBuilder.setDefault(
            transform(
              variable.lower.get().getHandleFor(explicitRepresentation.cacheView.defaultValue()),
              variable.lower.orElse(null),
              cache,
            )
              .node
          )
        } else {
          val cursor = explicitRepresentation.cacheView.cursor()
          while (cursor.moveNext()) {
            val s =
              transform(
                variable.lower.get().getHandleFor(cursor.value()),
                variable.lower.orElse(null),
                cache,
              )
            templateBuilder.set(cursor.key(), s.node)
          }
        }

        result = variable.checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset()))
      }

      //      if (
      //        structToSym.get(result) != null &&
      //          (node.node.representation as
      // MddExpressionRepresentation).explicitRepresentation.size != 0
      //      ) {
      //        println("Collision:")
      //        val expr1 =
      //          (structToSym.get(result)!!.node.representation as
      // MddExpressionRepresentation).expr
      //        val expr2 = (node.node.representation as MddExpressionRepresentation).expr
      //
      //        val expr1Canonized = ExprUtils.canonize(expr1)
      //        val expr2Canonized = ExprUtils.canonize(expr2)
      //        println(expr2Canonized.equals(expr1Canonized))
      //        println("expr1:" + expr1)
      //        println("expr2:" + expr2)
      //      }
      //      structToSym.put(result, node)
    }
    cache.addToCache(node, result)
    return result
  }
}
