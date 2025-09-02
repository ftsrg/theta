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
package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Factory class to instantiate different statements.
 *
 * @see Stmt
 */
@Suppress("FunctionName")
object Stmts {

  /** Create a skip statement */
  @JvmStatic fun Skip(): SkipStmt = SkipStmt

  /** Create an assume statement */
  @JvmStatic fun Assume(cond: Expr<BoolType>): AssumeStmt = AssumeStmt(cond)

  /** Create an assignment statement */
  @JvmStatic
  fun <T : Type> Assign(lhs: VarDecl<T>, rhs: Expr<T>): AssignStmt<T> = AssignStmt.of(lhs, rhs)

  /** Create a memory assignment statement */
  @JvmStatic
  fun <P : Type, O : Type, T : Type> MemoryAssign(
    deref: Dereference<P, O, T>,
    expr: Expr<T>,
  ): MemoryAssignStmt<P, O, T> = MemoryAssignStmt.of(deref, expr)

  /** Create a havoc statement */
  @JvmStatic fun <T : Type> Havoc(varDecl: VarDecl<T>): HavocStmt<T> = HavocStmt.of(varDecl)

  /** Create a sequence statement */
  @JvmStatic fun Sequence(stmts: List<Stmt>): SequenceStmt = SequenceStmt.of(stmts)

  /** Create a non-deterministic choice statement */
  @JvmStatic fun NonDet(stmts: List<Stmt>): NonDetStmt = NonDetStmt.of(stmts)
}
