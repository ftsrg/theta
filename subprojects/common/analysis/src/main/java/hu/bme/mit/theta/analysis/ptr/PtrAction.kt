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

package hu.bme.mit.theta.analysis.ptr

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils

private val varList = LinkedHashMap<String, LinkedHashMap<Int, VarDecl<IntType>>>()

abstract class PtrAction(writeTriples: WriteTriples, val inCnt: Int) : StmtAction() {

    abstract val stmtList: List<Stmt>

    private val expanded by lazy { createStmtList(writeTriples) }

    internal var cnts = LinkedHashMap<String, Int>()
    fun nextWriteTriples(tracked: Collection<Expr<*>> = TopCollection): WriteTriples =
        expanded.first.map { Pair(it.key, it.value.filter { it.toList().any(tracked::contains) }) }.toMap()

    final override fun getStmts(): List<Stmt> = expanded.second

    private fun createStmtList(writeTriples: WriteTriples): Pair<WriteTriples, List<Stmt>> {
        val nextWriteTriples = writeTriples.toMutable()
        val stmtList = ArrayList<Stmt>()
        val vargen = { it: String ->
            val current = cnts.getOrDefault(it, inCnt)
            cnts[it] = current + 1
            val iMap = varList.getOrPut(it) { LinkedHashMap() }
            iMap.getOrPut(current) { Var("__${it}_$current", Int()) }
        }
        for (stmt in this.stmtList.map { it.uniqueDereferences(vargen) }) {
            val preList = ArrayList<Stmt>()
            val postList = ArrayList<Stmt>()

            for ((deref, type) in stmt.dereferencesWithAccessTypes) {
                Preconditions.checkState(deref.uniquenessIdx.isPresent,
                    "Incomplete dereferences (missing uniquenessIdx) are not handled properly.")
                val list = nextWriteTriples[deref.type] ?: emptyList()
                val expr = list.fold(IntExprs.Int(0) as Expr<IntType>) { elze, (arr, off, value) ->
                    IteExpr.of(BoolExprs.And(
                        listOf(AbstractExprs.Eq(arr, deref.array), AbstractExprs.Eq(off, deref.offset))), value, elze)
                }
                if (type == AccessType.WRITE) {
                    val writeExpr = ExprUtils.simplify(IntExprs.Add(expr, IntExprs.Int(1)))
                    nextWriteTriples.getOrPut(deref.type) { ArrayList() }
                        .add(Triple(deref.array, deref.offset, deref.uniquenessIdx.get()))
                    postList.add(Stmts.Assume(ExprUtils.simplify(BoolExprs.And(listOf(
                        AbstractExprs.Eq(writeExpr, deref.uniquenessIdx.get()),
                    )))))
                } else {
                    preList.add(
                        Stmts.Assume(ExprUtils.simplify(AbstractExprs.Eq(expr, deref.uniquenessIdx.get()))))
                }
            }

            stmtList.addAll(preList)
            stmtList.add(stmt)
            stmtList.addAll(postList)
        }
        return Pair(nextWriteTriples, stmtList)
    }
}