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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.UnaryOperationCache
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*
import kotlin.jvm.optionals.getOrNull

object MddToExpr {

  val auxvarCache: UnaryOperationCache<MddHandle, VarDecl<BoolType>> =
    UnaryOperationCache()
  val constraintCache: UnaryOperationCache<MddHandle, Expr<BoolType>> =
    UnaryOperationCache()
  val expressionCache: UnaryOperationCache<MddHandle, Expr<BoolType>> =
    UnaryOperationCache()

  fun toExpr(root: MddHandle): Expr<BoolType> {
    // Return cached expression if present
    expressionCache.getOrNull(root)?.let { return it }

    // Traverse the MDD and collect unique nodes
    val visited = mutableSetOf<MddHandle>()
    val stack = ArrayDeque<MddHandle>()
    stack.add(root)

    while (stack.isNotEmpty()) {
      val node = stack.removeLast()
      if (visited.contains(node)) continue
      visited.add(node)

      // Ensure constraint (and auxiliary var) exists for this node
      getConstraintForNode(node)

      // If non-terminal, push children (including default)
      if (!node.isTerminal) {
        val cursor = node.cursor()
        while (cursor.moveNext()) {
          stack.add(cursor.value())
        }
        // defaultValue may be terminal or non-terminal; add it to traversal
        stack.add(node.defaultValue())
      }
    }
    val constraints = visited.map { constraintCache.getOrNull(it)!! }

    val rootVar = getVarForNode(root)
    var result: Expr<BoolType> = And(rootVar.ref, And(constraints))


    expressionCache.addToCache(root, result)
    return result
  }

  fun getVarForNode(node: MddHandle): VarDecl<BoolType> {
    auxvarCache.getOrNull(node)?.let { return it }

    val varDecl = Decls.Var("mdd_aux_${auxvarCache.cacheSize}", BoolType.getInstance())
    auxvarCache.addToCache(node, varDecl)
    return varDecl
  }

  fun getConstraintForNode(node: MddHandle): Expr<BoolType> {
    // Return existing auxiliary variable if already created
    constraintCache.getOrNull(node)?.let { return it }

    // Create auxiliary variable for this node
    val nodeVar = getVarForNode(node)

    val definition: Expr<BoolType> =
      if (node.isTerminal) {
        // Terminal definition
        if (node.isTerminalZero) {
          Eq(nodeVar.ref, False())
        } else {
          Eq(nodeVar.ref, True())
        }
      } else {
        if (node.defaultValue().isTerminalZero) {
          val x = node.variableHandle.variable.getOrNull()?.getTraceInfo(
            Decl::class.java)!!

          val disjuncts = mutableListOf<Expr<BoolType>>()

          val cursor = node.cursor()
          while (cursor.moveNext()) {

            val childVar = getVarForNode(cursor.value())

            val value = cursor.key()
            disjuncts +=
              And(Eq(x.ref, LitExprConverter.toLitExpr(value, x.type)), childVar.ref)
          }

          Eq(nodeVar.ref, Or(disjuncts))
        } else {
          Eq(nodeVar.ref, getVarForNode(node.defaultValue()).ref)
        }
      }

    constraintCache.addToCache(node, definition)
    return definition
  }
}
