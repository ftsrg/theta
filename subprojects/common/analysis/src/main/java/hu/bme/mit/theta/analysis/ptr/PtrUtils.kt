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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.TypeUtils


typealias WriteTriples = Map<Type, List<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>
typealias MutableWriteTriples = MutableMap<Type, MutableList<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>

fun WriteTriples.toMutable(): MutableWriteTriples =
    LinkedHashMap(this.map { Pair(it.key, ArrayList(it.value)) }.toMap())

enum class AccessType {
    READ, WRITE
}

val Stmt.dereferencesWithAccessTypes: List<Pair<Dereference<*, *>, AccessType>>
    get() = when (this) {
        is MemoryAssignStmt<*, *> -> expr.dereferences.map { Pair(it, AccessType.READ) } + listOf(
            Pair(deref, AccessType.WRITE))

        is AssignStmt<*> -> expr.dereferences.map { Pair(it, AccessType.READ) }
        is AssumeStmt -> cond.dereferences.map { Pair(it, AccessType.READ) }
        is SequenceStmt -> stmts.flatMap { it.dereferencesWithAccessTypes }
        is HavocStmt<*> -> listOf()
        is SkipStmt -> listOf()
        is NonDetStmt -> error("NonDetStmts do not have a clearly defined sequence")
        is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
        is IfStmt -> error("IfStmt do not have a clearly defined sequence")
        else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }

val Expr<*>.dereferences: List<Dereference<*, *>>
    get() = if (this is Dereference<*, *>) {
        listOf(this)
    } else {
        ops.flatMap { it.dereferences }
    }


fun SequenceStmt.collapse(): Stmt =
    if (stmts.size == 1 && stmts[0] is SequenceStmt) {
        (stmts[0] as SequenceStmt).collapse()
    } else if (stmts.size == 1) {
        stmts[0]
    } else {
        this
    }

fun Stmt.uniqueDereferences(vargen: (String) -> VarDecl<IntType>): Stmt {
    val ret = ArrayList<Stmt>()
    val newStmt = when (this) {
        is MemoryAssignStmt<*, *> -> {
            MemoryAssignStmt.create(
                deref.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second as Dereference<*, *>,
                expr.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second)
        }

        is AssignStmt<*> -> AssignStmt.of(
            TypeUtils.cast(varDecl, varDecl.type),
            TypeUtils.cast(expr.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second, varDecl.type))

        is AssumeStmt -> AssumeStmt.of(cond.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second)
        is SequenceStmt -> Stmts.SequenceStmt(stmts.map { it.uniqueDereferences(vargen) })
        is HavocStmt<*> -> this
        is SkipStmt -> this
        is NonDetStmt -> error("NonDetStmts do not have a clearly defined sequence")
        is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
        is IfStmt -> error("IfStmt do not have a clearly defined sequence")
        else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }
    return SequenceStmt.of(ret + newStmt).collapse()
}

fun <T : Type> Expr<T>.uniqueDereferences(vargen: (String) -> VarDecl<IntType>): Pair<List<Stmt>, Expr<T>> =
    if (this is Dereference<*, T>) {
        val ret = ArrayList<Stmt>()
        Preconditions.checkState(this.uniquenessIdx.isEmpty, "Only non-pretransformed dereferences should be here")
        val arrayConst = vargen("a")
        val offsetConst = vargen("o")
        val newList = listOf(
            Stmts.Assume(Eq(arrayConst.ref, array.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second)),
            Stmts.Assume(Eq(offsetConst.ref, offset.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second)),
        )
        Pair(
            ret + newList,
            Exprs.Dereference(arrayConst.ref, offsetConst.ref, type).withUniquenessExpr(vargen("idx").ref))
    } else {
        val ret = ArrayList<Stmt>()
        Pair(ret, this.withOps(this.ops.map { it.uniqueDereferences(vargen).also { ret.addAll(it.first) }.second }))
    }

object TopCollection: Collection<Expr<*>> {
    override val size: Int
        get() = error("No size information known for TopCollection")

    override fun contains(element: Expr<*>): Boolean = true

    override fun containsAll(elements: Collection<Expr<*>>) = true

    override fun isEmpty(): Boolean = false

    override fun iterator(): Iterator<Expr<*>> = error("TopCollection not iterable")
}

enum class PtrTracking {
    ALWAYS_TOP, // always keep track of all pointer accesses
    ANY_MATCH, // if any of the arguments match, keep track
    ALL_MATCH, // if all of the arguments match, keep track
    NONE // do not keep track of any pointer acceses
}