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
package hu.bme.mit.theta.analysis.ptr

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.utils.ExprUtils

private val varList = LinkedHashMap<Pair<String, Type>, LinkedHashMap<Int, VarDecl<*>>>()

abstract class PtrAction(writeTriples: WriteTriples = emptyMap(), val inCnt: Int = 0) :
  StmtAction() {

  abstract val stmtList: List<Stmt>

  private val expanded by lazy { createStmtList(writeTriples) }

  var cnts = LinkedHashMap<String, Int>()

  fun nextWriteTriples(): WriteTriples = expanded.first

  final override fun getStmts(): List<Stmt> = expanded.second

  fun havocStmts(): List<Stmt> = expanded.third

  private fun createStmtList(
    writeTriples: WriteTriples
  ): Triple<WriteTriples, List<Stmt>, List<Stmt>> {
    val nextWriteTriples = writeTriples.toMutable()
    val havocStmtList = ArrayList<Stmt>()
    val stmtList = ArrayList<Stmt>()
    val vargen = { it: String, type: Type ->
      val current = cnts.getOrDefault(it, inCnt)
      cnts[it] = current + 1
      val iMap = varList.getOrPut(Pair(it, type)) { LinkedHashMap() }
      iMap.getOrPut(current) { Var("__${it}_$current", type) }
    }
    val lookup = LinkedHashMap<Dereference<*, *, *>, Pair<Expr<*>, Expr<*>>>()
    for (stmt in this.stmtList.map { it.uniqueDereferences(vargen, lookup) }) {
      val preList = ArrayList<Stmt>()
      val postList = ArrayList<Stmt>()

      for ((deref, type) in stmt.dereferencesWithAccessTypes) {
        Preconditions.checkState(
          deref.uniquenessIdx.isPresent,
          "Incomplete dereferences (missing uniquenessIdx) are not handled properly.",
        )
        val expr = deref.getIte(nextWriteTriples)
        if (type == AccessType.WRITE) {
          val writeExpr = ExprUtils.simplify(IntExprs.Add(expr, IntExprs.Int(1)))
          nextWriteTriples
            .getOrPut(deref.type) { ArrayList() }
            .add(Triple(lookup[deref]!!.first, lookup[deref]!!.second, deref.uniquenessIdx.get()))
          postList.add(
            Stmts.Assume(
              ExprUtils.simplify(
                BoolExprs.And(listOf(AbstractExprs.Eq(writeExpr, deref.uniquenessIdx.get())))
              )
            )
          )
        } else {
          preList.add(
            Stmts.Assume(ExprUtils.simplify(AbstractExprs.Eq(expr, deref.uniquenessIdx.get())))
          )
        }
        //                postList.add(Stmts.Assume(Eq(vargen("value", deref.type).ref, deref))) //
        // debug mode
      }

      stmtList.addAll(preList)
      stmtList.add(stmt)
      havocStmtList.add(stmt)
      stmtList.addAll(postList)
    }
    return Triple(nextWriteTriples, stmtList, havocStmtList)
  }
}
