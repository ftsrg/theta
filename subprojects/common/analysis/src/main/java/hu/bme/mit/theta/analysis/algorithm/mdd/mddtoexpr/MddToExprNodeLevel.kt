/*
 *  Copyright 2025-2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.mddtoexpr

import hu.bme.mit.delta.java.mdd.BinaryOperationCache
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariable
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*

object MddToExprNodeLevel : MddToExpr {

  val auxvarCache: BinaryOperationCache<MddNode, MddVariable, Decl<BoolType>> =
    BinaryOperationCache()
  val constraintCache: BinaryOperationCache<MddNode, MddVariable, Expr<BoolType>> =
    BinaryOperationCache()
  val expressionCache: BinaryOperationCache<MddNode, MddVariable, Expr<BoolType>> =
    BinaryOperationCache()

  override fun toExpr(root: MddHandle): Expr<BoolType> =
    toExpr(root.node, root.variableHandle.variable.orElseThrow())

  fun toExpr(root: MddNode, variable: MddVariable): Expr<BoolType> {
    // Return cached expression if present
    expressionCache.getOrNull(root, variable)?.let {
      return it
    }

    // Traverse the MDD and collect unique (node, variable) pairs
    val visited = mutableSetOf<Pair<MddNode, MddVariable>>()
    val stack = ArrayDeque<Pair<MddNode, MddVariable>>()
    stack.add(Pair(root, variable))

    while (stack.isNotEmpty()) {
      val (node, varNode) = stack.removeLast()
      val pair = Pair(node, varNode)
      if (visited.contains(pair)) continue
      visited.add(pair)

      // Ensure constraint (and auxiliary var) exists for this node-variable pair
      getConstraintForNode(node, varNode)

      // If non-terminal, push children (including default) with the next variable
      if (!node.isTerminal && varNode.lower.isPresent) {
        val nextVar = varNode.lower.orElseThrow()
        val defaultNode = node.defaultValue()
        if (defaultNode != null) {
          stack.add(Pair(defaultNode, nextVar))
        } else {
          val cursor = node.cursor()
          while (cursor.moveNext()) {
            stack.add(Pair(cursor.value(), nextVar))
          }
        }
      }
    }
    val constraints = visited.map { (n, v) -> constraintCache.getOrNull(n, v)!! }

    val rootRepresentative = getRepresentativeForNode(root, variable)
    val result: Expr<BoolType> = And(rootRepresentative, And(constraints))

    expressionCache.addToCache(root, variable, result)
    return result
  }

  fun getRepresentativeForNode(node: MddNode, variable: MddVariable?): Expr<BoolType> {
    if (node.isTerminal) return True()
    else {
      auxvarCache.getOrNull(node, variable)?.let {
        return it.ref
      }

      val varDecl = Decls.Var("mddnode_${auxvarCache.cacheSize}", BoolType.getInstance())
      val constDecl = varDecl.getConstDecl(0)
      auxvarCache.addToCache(node, variable, constDecl)
      return constDecl.ref
    }
  }

  fun getConstraintForNode(node: MddNode, variable: MddVariable): Expr<BoolType> {
    // Return existing constraint if already created
    constraintCache.getOrNull(node, variable)?.let {
      return it
    }

    val representative = getRepresentativeForNode(node, variable)

    val definition: Expr<BoolType> =
      if (node.isTerminal) {
        // Terminal definition
        return representative
      } else {
        if (node.defaultValue() == null) {
          val x = variable.getTraceInfo(Decl::class.java)!!

          val disjuncts = mutableListOf<Expr<BoolType>>()

          val cursor = node.cursor()
          while (cursor.moveNext()) {

            val childRepresentative =
              getRepresentativeForNode(cursor.value(), variable.lower.orElse(null))

            val value = cursor.key()
            disjuncts +=
              And(Eq(x.ref, LitExprConverter.toLitExpr(value, x.type)), childRepresentative)
          }

          Eq(representative, Or(disjuncts))
        } else {
          Eq(
            representative,
            getRepresentativeForNode(node.defaultValue(), variable.lower.orElseThrow()),
          )
        }
      }

    constraintCache.addToCache(node, variable, definition)
    return definition
  }
}
