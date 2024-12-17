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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.util

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.ExprUtils

/**
 * Collects vars from a statement to a fixpoint. Collects recursively only variables that are
 * dependant on the input set on themselves. To collect all variables from a statement, use
 * [hu.bme.mit.theta.core.utils.StmtUtils.getVars] instead.
 */
class VarCollectorStmtVisitor : StmtVisitor<Set<VarDecl<*>>, Set<VarDecl<*>>> {

  companion object {

    fun visitAll(stmts: Collection<Stmt>, vars: Set<VarDecl<*>>): Set<VarDecl<*>> {
      val visitor = VarCollectorStmtVisitor()
      val expanded: Set<VarDecl<*>> =
        stmts.fold(emptySet()) { acc, stmt -> acc + stmt.accept(visitor, vars) }
      return if (expanded.size > vars.size) visitAll(stmts, expanded) else expanded
    }
  }

  override fun visit(stmt: SkipStmt, param: Set<VarDecl<*>>) = param

  override fun visit(stmt: AssumeStmt, param: Set<VarDecl<*>>) = param

  override fun <DeclType : Type> visit(
    stmt: AssignStmt<DeclType>,
    param: Set<VarDecl<*>>,
  ): Set<VarDecl<*>> {
    val rightVars: Collection<VarDecl<*>> = ExprUtils.getVars(stmt.expr)
    val leftVar = stmt.varDecl
    for (rightVar in rightVars) {
      if (rightVar == leftVar || param.contains(rightVar)) {
        return param.plus(leftVar)
      }
    }
    return param
  }

  override fun <DeclType : Type> visit(stmt: HavocStmt<DeclType>, param: Set<VarDecl<*>>) =
    param + stmt.varDecl

  override fun visit(stmt: SequenceStmt, param: Set<VarDecl<*>>) =
    param + visitAll(stmt.stmts, param)

  override fun visit(stmt: NonDetStmt, param: Set<VarDecl<*>>) = param + visitAll(stmt.stmts, param)

  override fun visit(stmt: OrtStmt, param: Set<VarDecl<*>>) = param + visitAll(stmt.stmts, param)

  override fun visit(stmt: LoopStmt, param: Set<VarDecl<*>>) = param + stmt.stmt.accept(this, param)

  override fun visit(stmt: IfStmt, param: Set<VarDecl<*>>) =
    param + stmt.then.accept(this, param) + stmt.elze.accept(this, param)

  override fun <PtrType : Type?, OffsetType : Type?, DeclType : Type?> visit(
    stmt: MemoryAssignStmt<PtrType, OffsetType, DeclType>?,
    param: Set<VarDecl<*>>?,
  ): Set<VarDecl<*>> {
    TODO("Not yet implemented")
  }
}
