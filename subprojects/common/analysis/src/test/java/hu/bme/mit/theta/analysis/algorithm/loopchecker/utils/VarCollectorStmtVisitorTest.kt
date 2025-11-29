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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.utils

import hu.bme.mit.theta.analysis.algorithm.loopchecker.util.VarCollectorStmtVisitor
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import java.util.*
import org.junit.Assert
import org.junit.Test
import org.junit.jupiter.api.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class VarCollectorStmtVisitorTest(
  private val stmt: Stmt,
  private val inputVars: Set<VarDecl<*>>,
  private val expectedVars: Set<VarDecl<*>>,
) {

  @Test
  fun test() {
    val vars = VarCollectorStmtVisitor.visitAll(listOf(stmt), inputVars)
    Assert.assertEquals(expectedVars, vars)
  }

  companion object {

    private val VA: VarDecl<BoolType?> = Decls.Var("a", BoolExprs.Bool())
    private val VB: VarDecl<IntType?> = Decls.Var("b", IntExprs.Int())
    private val VC: VarDecl<IntType?> = Decls.Var("d", IntExprs.Int())

    @JvmStatic
    @Parameterized.Parameters
    fun data(): Collection<Array<Any>> {
      return listOf(
        arrayOf(Stmts.Skip(), emptySet<VarDecl<*>>(), emptySet<VarDecl<*>>()),
        arrayOf(Stmts.Havoc(VA), emptySet<VarDecl<*>>(), setOf(VA)),
        arrayOf(Stmts.Havoc(VB), emptySet<VarDecl<*>>(), setOf(VB)),
        arrayOf(Stmts.Havoc(VA), setOf(VA), setOf(VA)),
        arrayOf(Stmts.Havoc(VB), setOf(VA), setOf(VA, VB)),
        arrayOf(Stmts.Assign(VB, IntExprs.Int(0)), setOf(VB), setOf(VB)),
        arrayOf(Stmts.Assign(VB, IntExprs.Add(VB.ref, IntExprs.Int(1))), setOf(VB), setOf(VB)),
        arrayOf(Stmts.Assign(VB, IntExprs.Add(VC.ref, VC.ref)), setOf(VC), setOf(VB, VC)),
        arrayOf(
          Stmts.Assume(BoolExprs.And(VA.ref, IntExprs.Eq(VB.ref, VC.ref))),
          setOf(VC),
          setOf(VC),
        ),
        arrayOf(IfStmt.of(BoolExprs.False(), Stmts.Havoc(VB)), emptySet<VarDecl<*>>(), setOf(VB)),
      )
    }
  }
}
