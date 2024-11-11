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
package hu.bme.mit.theta.xsts.analysis

import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.xsts.XSTS

fun XSTS.orderVars(): List<VarDecl<*>> {
  val flattened = flattenStmts(tran)
  val orderedVars = orderVarsFromRandomStartingPoints(this.stateVars.toList(), flattened)
  return orderedVars
}

fun cartesianProduct(vararg sets: Set<*>): Set<List<*>> =
  sets
    .fold(listOf(listOf<Any?>())) { acc, set ->
      acc.flatMap { list -> set.map { element -> list + element } }
    }
    .toSet()

private fun flattenStmts(stmt: Stmt): Set<Stmt> {
  return when (stmt) {
    is NonDetStmt -> {
      stmt.stmts.flatMap { flattenStmts(it) }.toSet()
    }
    is SequenceStmt -> {
      cartesianProduct(*(stmt.stmts.map { flattenStmts(it) }.toTypedArray()))
        .map { SequenceStmt.of(it as List<Stmt>) }
        .toSet()
    }
    is IfStmt -> {
      flattenStmts(stmt.then) + flattenStmts(stmt.elze)
    }
    else -> {
      setOf(stmt)
    }
  }
}

// private fun collectStmts(stmt: Stmt): Set<Stmt> {
//    return when(stmt) {
//        is NonDetStmt -> {
//            stmt.stmts.flatMap { collectStmts(it) }.toSet()
//        }
//        is SequenceStmt -> {
//            stmt.stmts.flatMap { collectStmts(it) }.toSet()
//        }
//        else -> {
//           setOf(stmt)
//        }
//    }
// }
