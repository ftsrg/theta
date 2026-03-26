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
package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType

enum class EventType {
  WRITE,
  READ,
}

abstract class Event(
  val const: IndexedConstDecl<*>,
  val type: EventType,
  var guard: Set<Expr<BoolType>>,
  val pid: Int,
  val clkId: Int,
) {
  companion object {
    var clkSize = 0
      private set
  }

  init {
    if (clkId >= clkSize) {
      clkSize = clkId + 1
    }
  }

  val guardExpr: Expr<BoolType>
    get() = guard.toAnd()

  var assignment: Expr<BoolType>? = null

  open fun enabled(valuation: Valuation): Boolean? = tryOrNull {
    (guardExpr.eval(valuation) as? BoolLitExpr)?.value
  }

  open fun sameMemory(other: Event): Boolean {
    if (this === other) return true
    return const.varDecl == other.const.varDecl
  }

  open fun interferenceCond(other: Event): Expr<BoolType>? = null

  protected inline fun <T> tryOrNull(block: () -> T?): T? =
    try {
      block()
    } catch (_: Exception) {
      null
    }

  override fun toString(): String {
    return "Event(pid=$pid, clkId=$clkId, ${const.name}[${type.toString()[0]}], guard=$guard)"
  }
}

enum class RelationType {
  PO,
  RF,
  WS,
}

data class Relation<E : Event>(val type: RelationType, val from: E, val to: E) {

  val decl: ConstDecl<BoolType> =
    Decls.Const(
      "${type.toString().lowercase()}_${from.const.name}_${to.const.name}",
      BoolExprs.Bool(),
    )
  val declRef: RefExpr<BoolType> = RefExpr.of(decl)

  override fun toString() =
    "Relation($type, ${from.const.name}[${from.type.toString()[0]}], ${to.const.name}[${to.type.toString()[0]}])"

  fun enabled(valuation: Map<Decl<*>, LitExpr<*>>): Boolean? =
    if (type == RelationType.PO) true else valuation[decl]?.let { (it as BoolLitExpr).value }
}
