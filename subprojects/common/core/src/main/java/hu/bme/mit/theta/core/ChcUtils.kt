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
package hu.bme.mit.theta.core

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import java.util.*

/*
We want to be able to write logical derivations in the following way:

head_name(vars) +=  // derivations
    expr(vars).

head_name(grounds) // facts

!head_name(vars) with exprs(vars)  // queries
 */

open class Relation(val name: String, vararg paramTypes: Type) {
  companion object {

    private fun funcType(params: List<Type>, finalType: Type): FuncType<*, *> {
      return if (params.size == 1) {
        FuncType.of(params[0], finalType)
      } else if (params.size > 1) {
        FuncType.of(params[0], funcType(params.subList(1, params.size), finalType))
      } else {
        error("Nullary functions aren't handled here.")
      }
    }
  }

  val arity: Int = paramTypes.size
  val rules: MutableList<Rule> = LinkedList()
  val constDecl = Const(name, funcType(paramTypes.toList(), Bool()))

  open operator fun invoke(params: List<Expr<*>>) = RelationApp(this, params)

  open operator fun invoke(vararg params: Expr<*>) = RelationApp(this, params.toList())
}

data class RelationApp(
  val relation: Relation,
  val params: List<Expr<*>>,
  val constraints: List<Expr<BoolType>> = emptyList(),
) {

  init {
    checkArgument(params.size == relation.arity)
  }

  val expr: Expr<BoolType> by lazy {
    val coreExpr =
      if (params.size >= 1) {
        FuncExprs.App(
          relation.constDecl.ref as Expr<FuncType<in Type, BoolType>>,
          params.map { it },
        )
      } else {
        relation.constDecl.ref as Expr<BoolType>
      }
    if (constraints.isEmpty()) {
      coreExpr
    } else {
      And(constraints + coreExpr)
    }
  }

  operator fun plusAssign(constraints: List<Expr<BoolType>>) {
    relation.rules.add(Rule(expr, constraints))
  }

  operator fun plusAssign(constraint: Expr<BoolType>) {
    relation.rules.add(Rule(expr, listOf(constraint)))
  }

  operator fun not() {
    relation.rules.add(Rule(False(), listOf(expr)))
  }

  operator fun unaryPlus() {
    relation.rules.add(Rule(expr, listOf()))
  }

  infix fun with(constraints: List<Expr<BoolType>>) =
    copy(constraints = this.constraints + constraints)

  infix fun with(constraint: Expr<BoolType>) = copy(constraints = this.constraints + constraint)
}

data class Rule(val head: Expr<BoolType>, val constraints: List<Expr<BoolType>>) {

  fun toExpr(): Expr<BoolType> {
    val params = ExprUtils.getParams(head) + ExprUtils.getParams(constraints)
    val nontrivialConstraints = constraints.filter { it != True() }
    return if (params.isNotEmpty()) {
      Forall(params, Imply(And(nontrivialConstraints), head))
    } else if (nontrivialConstraints.isNotEmpty()) {
      Forall(listOf(Param("__dummy__", Int())), Imply(And(nontrivialConstraints), head))
    } else {
      head
    }
  }
}

operator fun Expr<BoolType>.plus(other: Expr<BoolType>) = listOf(this, other)

data class ParamHolder<T : Type>(private val type: T) {

  private val lookup = LinkedHashMap<Int, ParamDecl<T>>()

  operator fun get(i: Int) = lookup.getOrPut(i) { Param("P$i", type) }.ref
}
