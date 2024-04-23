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
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast

typealias WriteTriples = Map<Type, List<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>
typealias MutableWriteTriples = MutableMap<Type, MutableList<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>

private var cnt = 0

data class PtrAction(private val stmtList: List<Stmt>, private val writeTriples: WriteTriples): StmtAction() {

    private val nextWriteTriples: MutableWriteTriples = writeTriples.toMutable()
    private val expandedStmtList: List<Stmt> = createStmtList()

    fun getNextWriteTriples(): WriteTriples = nextWriteTriples

    private fun createStmtList(): List<Stmt> {
        val stmtList = ArrayList<Stmt>()
        for (stmt in this.stmtList.map(Stmt::uniqueDereferences)) {
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
                    val freshArrayCopy = Decls.Var("__deref__helper_${cnt++}", deref.array.type)
                    val freshOffsetCopy = Decls.Var("__deref__helper_${cnt++}", deref.offset.type)
                    nextWriteTriples.getOrPut(deref.type) { ArrayList() }
                        .add(Triple(freshArrayCopy.ref, freshOffsetCopy.ref, deref.uniquenessIdx.get()))
                    postList.add(Stmts.Assume(ExprUtils.simplify(BoolExprs.And(listOf(
                        AbstractExprs.Eq(writeExpr, deref.uniquenessIdx.get()),
                        AbstractExprs.Eq(freshArrayCopy.ref, deref.array),
                        AbstractExprs.Eq(freshOffsetCopy.ref, deref.offset),
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
        return stmtList
    }

    override fun getStmts(): List<Stmt> = expandedStmtList
}

private fun WriteTriples.toMutable(): MutableWriteTriples =
    LinkedHashMap(this.map { Pair(it.key, ArrayList(it.value)) }.toMap())

private enum class AccessType {
    READ, WRITE
}

private val Stmt.dereferencesWithAccessTypes: List<Pair<Dereference<*, *>, AccessType>>
    get() = when (this) {
        is MemoryAssignStmt<*, *> -> expr.dereferences.map { Pair(it, AccessType.READ) } + listOf(Pair(deref, AccessType.WRITE))
        is AssignStmt<*> -> expr.dereferences.map { Pair(it, AccessType.READ) }
        is AssumeStmt -> cond.dereferences.map { Pair(it, AccessType.READ) }
        is SequenceStmt -> stmts.flatMap(Stmt::dereferencesWithAccessTypes)
        is HavocStmt<*> -> listOf()
        is NonDetStmt -> error("NonDetStmts do not have a clearly defined sequence")
        is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
        is IfStmt -> error("IfStmt do not have a clearly defined sequence")
        else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }

private val Expr<*>.dereferences: List<Dereference<*, *>>
    get() = if (this is Dereference<*, *>) {
        listOf(this)
    } else {
        ops.flatMap { it.dereferences }
    }


private fun SequenceStmt.collapse(): Stmt =
    if(stmts.size == 1 && stmts[0] is SequenceStmt) {
        (stmts[0] as SequenceStmt).collapse()
    } else if (stmts.size == 1) {
        stmts[0]
    } else {
        this
    }

private fun Stmt.uniqueDereferences(): Stmt {
    val ret = ArrayList<Stmt>()
    val newStmt = when (this) {
        is MemoryAssignStmt<*, *> -> {
            MemoryAssignStmt.create(deref.uniqueDereferences().also { ret.addAll(it.first) }.second as Dereference<*, *>, expr.uniqueDereferences().also { ret.addAll(it.first) }.second)
        }
        is AssignStmt<*> -> AssignStmt.of(
            cast(varDecl, varDecl.type),
            cast(expr.uniqueDereferences().also { ret.addAll(it.first) }.second, varDecl.type))
        is AssumeStmt -> AssumeStmt.of(cond.uniqueDereferences().also { ret.addAll(it.first) }.second)
        is SequenceStmt -> SequenceStmt(stmts.map(Stmt::uniqueDereferences))
        is HavocStmt<*> -> this
        is NonDetStmt -> error("NonDetStmts do not have a clearly defined sequence")
        is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
        is IfStmt -> error("IfStmt do not have a clearly defined sequence")
        else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }
    return SequenceStmt.of(ret + newStmt).collapse()
}

private fun <T: Type> Expr<T>.uniqueDereferences(): Pair<List<Stmt>, Expr<T>> =
    if (this is Dereference<*, T>) {
        checkState(this.uniquenessIdx.isEmpty, "Only non-pretransformed dereferences should be here")
        val arrayConst = Decls.Var("__deref__helper_${cnt++}", array.type)
        val offsetConst = Decls.Var("__deref__helper_${cnt++}", offset.type)
        Pair(
            listOf(
                Assign(cast(arrayConst, array.type), cast(array, array.type)),
                Assign(cast(offsetConst, offset.type), cast(offset, offset.type)),
            ),
            Dereference(arrayConst.ref, offsetConst.ref, type).withFreshVar())
    } else {
        val ret = ArrayList<Stmt>()
        Pair(ret, this.withOps(this.ops.map { it.uniqueDereferences().also { ret.addAll(it.first) }.second }))
    }