/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast

fun Stmt.changeVars(variableMapping: Map<String, VarDecl<*>>): Stmt {
  return when (this) {
    is AssignStmt<*> ->
      AssignStmt.of(
        cast(varDecl.changeVars(variableMapping), varDecl.type),
        cast(expr.changeVars(variableMapping), varDecl.type),
      )

    is HavocStmt<*> -> HavocStmt.of(varDecl.changeVars(variableMapping))
    is AssumeStmt -> AssumeStmt.of(cond.changeVars(variableMapping))
    is SequenceStmt -> SequenceStmt.of(stmts.map { it.changeVars(variableMapping) })
    is SkipStmt -> this
    is NonDetStmt -> NonDetStmt.of(stmts.map { it.changeVars(variableMapping) })
    is LoopStmt ->
      LoopStmt.of(
        stmt.changeVars(variableMapping),
        loopVariable.changeVars(variableMapping),
        from.changeVars(variableMapping),
        to.changeVars(variableMapping),
      )

    is IfStmt ->
      IfStmt.of(
        cond.changeVars(variableMapping),
        then.changeVars(variableMapping),
        elze.changeVars(variableMapping),
      )

    else -> TODO("Not yet implemented")
  }
}

fun <T : Type> Expr<T>.changeVars(variableMapping: Map<String, VarDecl<*>>): Expr<T> =
  if (this is RefExpr<T>) {
    when (this.decl) {
      is VarDecl<T> -> (this.decl as VarDecl<T>).changeVars(variableMapping).ref
      else -> this
    }
  } else this.withOps(this.ops.map { it.changeVars(variableMapping) })

@SuppressWarnings("kotlin:S6530")
fun <T : Type> VarDecl<T>.changeVars(variableMapping: Map<String, VarDecl<*>>): VarDecl<T> {
  val swap = variableMapping[this.name] ?: return this
  if (swap.type != this.type) throw RuntimeException("Can't change variable to different type")
  return swap as VarDecl<T>
}
