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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntDivExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.core.type.inttype.IntMulExpr
import hu.bme.mit.theta.core.type.inttype.IntRemExpr
import hu.bme.mit.theta.core.type.rattype.RatDivExpr
import hu.bme.mit.theta.core.type.rattype.RatMulExpr
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.xcfa.model.*

/**
 * The arithmetic traits of a model that was not built from C, read off the sorts and operators left
 * in it. Nonlinear real arithmetic counts as [ArithmeticTrait.NONLIN_INT]. As in the C frontend,
 * [ArithmeticTrait.LIN_INT] is never added: it is what the absence of the others means.
 */
fun XCFA.collectArithmeticTraits(): Set<ArithmeticTrait> {
  val traits = mutableSetOf<ArithmeticTrait>()
  collectVars().forEach { traits.addTypeTraits(it.type) }

  val stack = ArrayDeque<Expr<*>>()
  procedures.forEach { procedure -> procedure.edges.forEach { stack.addAll(it.label.exprs()) } }
  val seen = mutableSetOf<Expr<*>>()
  while (stack.isNotEmpty()) {
    val expr = stack.removeLast()
    if (!seen.add(expr)) continue
    traits.addTypeTraits(expr.type)
    traits.addOperatorTraits(expr)
    stack.addAll(expr.ops)
  }
  return traits
}

private fun MutableSet<ArithmeticTrait>.addTypeTraits(type: Type) {
  when (type) {
    is FpType -> add(ArithmeticTrait.FLOAT)
    is BvType -> add(ArithmeticTrait.BITWISE)
    is ArrayType<*, *> -> {
      add(ArithmeticTrait.ARR)
      addTypeTraits(type.indexType)
      addTypeTraits(type.elemType)
    }
    is FuncType<*, *> -> {
      addTypeTraits(type.paramType)
      addTypeTraits(type.resultType)
    }
  }
}

private fun MutableSet<ArithmeticTrait>.addOperatorTraits(expr: Expr<*>) {
  when (expr) {
    is IntMulExpr,
    is RatMulExpr -> if (expr.ops.count { !it.isConstant() } > 1) add(ArithmeticTrait.NONLIN_INT)
    is IntDivExpr,
    is IntModExpr,
    is IntRemExpr ->
      if (!expr.ops[1].isConstant()) {
        add(ArithmeticTrait.NONLIN_INT)
        add(ArithmeticTrait.NONCONST_DIV)
      }
    is RatDivExpr -> if (!expr.ops[1].isConstant()) add(ArithmeticTrait.NONLIN_INT)
  }
}

private fun Expr<*>.isConstant(): Boolean =
  this is LitExpr<*> || (this !is RefExpr<*> && ops.isNotEmpty() && ops.all { it.isConstant() })

private fun XcfaLabel.exprs(): List<Expr<*>> =
  when (this) {
    is StmtLabel -> stmt.exprs()
    is SequenceLabel -> labels.flatMap { it.exprs() }
    is NondetLabel -> labels.flatMap { it.exprs() }
    is ReturnLabel -> enclosedLabel.exprs()
    is InvokeLabel -> params
    is StartLabel -> params
    else -> emptyList()
  }

private fun Stmt.exprs(): List<Expr<*>> =
  when (this) {
    is AssignStmt<*> -> listOf(expr)
    is AssumeStmt -> listOf(cond)
    is MemoryAssignStmt<*, *, *> -> listOf(deref, expr)
    else -> emptyList()
  }
