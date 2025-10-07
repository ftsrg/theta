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
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils

typealias WriteTriples = Map<Type, List<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>

typealias MutableWriteTriples =
  MutableMap<Type, MutableList<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>

fun WriteTriples.toMutable(): MutableWriteTriples =
  LinkedHashMap(this.map { Pair(it.key, ArrayList(it.value)) }.toMap())

enum class AccessType {
  READ,
  WRITE,
}

val Stmt.dereferencesWithAccessTypes: List<Pair<Dereference<*, *, *>, AccessType>>
  get() =
    when (this) {
      is MemoryAssignStmt<*, *, *> ->
        expr.dereferences.map { Pair(it, AccessType.READ) } +
          listOf(Pair(deref, AccessType.WRITE)) +
          deref.ops.flatMap { it.dereferences }.map { Pair(it, AccessType.READ) }

      is AssignStmt<*> -> expr.dereferences.map { Pair(it, AccessType.READ) }
      is AssumeStmt -> cond.dereferences.map { Pair(it, AccessType.READ) }
      is SequenceStmt -> stmts.flatMap { it.dereferencesWithAccessTypes }
      is HavocStmt<*> -> listOf()
      is SkipStmt -> listOf()
      is NonDetStmt -> listOf()
      is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
      is IfStmt -> error("IfStmt do not have a clearly defined sequence")
      else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }

val Expr<*>.dereferences: List<Dereference<*, *, *>>
  get() =
    if (this is Dereference<*, *, *>) {
      listOf(this) + ops.flatMap { it.dereferences }
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

fun Stmt.uniqueDereferences(
  vargen: (String, Type) -> VarDecl<*>,
  lookup: MutableMap<Dereference<*, *, *>, Pair<Expr<*>, Expr<*>>>,
): Stmt {
  val ret = ArrayList<Stmt>()
  val newStmt =
    when (this) {
      is MemoryAssignStmt<*, *, *> -> {
        MemoryAssignStmt.create(
          deref.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second
            as Dereference<*, *, *>,
          expr.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second,
        )
      }

      is AssignStmt<*> ->
        AssignStmt.of(
          TypeUtils.cast(varDecl, varDecl.type),
          TypeUtils.cast(
            expr.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second,
            varDecl.type,
          ),
        )

      is AssumeStmt ->
        AssumeStmt.of(cond.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second)
      is SequenceStmt -> Stmts.SequenceStmt(stmts.map { it.uniqueDereferences(vargen, lookup) })
      is HavocStmt<*> -> this
      is SkipStmt -> this
      is NonDetStmt -> this
      is LoopStmt -> error("LoopStmt do not have a clearly defined sequence")
      is IfStmt -> error("IfStmt do not have a clearly defined sequence")
      else -> TODO("Not yet implemented for ${this.javaClass.simpleName}")
    }
  return SequenceStmt.of(ret + newStmt).collapse()
}

fun <T : Type> Expr<T>.uniqueDereferences(
  vargen: (String, Type) -> VarDecl<*>,
  lookup: MutableMap<Dereference<*, *, *>, Pair<Expr<*>, Expr<*>>>,
): Pair<List<Stmt>, Expr<T>> =
  if (this is Dereference<*, *, T>) {
    val ret = ArrayList<Stmt>()
    Preconditions.checkState(
      this.uniquenessIdx.isEmpty,
      "Only non-pretransformed dereferences should be here",
    )
    val arrayExpr =
      ExprUtils.simplify(
        array.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second
      )
    val arrayLaterRef =
      if (arrayExpr !is LitExpr<*>) {
        val arrayConst = vargen("a", array.type).ref
        ret.add(Assume(Eq(arrayConst, arrayExpr)))
        arrayConst
      } else {
        arrayExpr
      }
    val offsetExpr =
      ExprUtils.simplify(
        offset.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second
      )
    val offsetLaterRef =
      if (offsetExpr !is LitExpr<*>) {
        val offsetConst = vargen("o", offset.type).ref
        ret.add(Assume(Eq(offsetConst, offsetExpr)))
        offsetConst
      } else {
        offsetExpr
      }
    val deref = withUniquenessExpr(vargen("idx", Int()).ref as Expr<IntType>)
    val retDeref =
      deref.map { it.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second }
        as Dereference<*, *, T>
    lookup[retDeref] = Pair(arrayLaterRef, offsetLaterRef)
    Pair(ret, retDeref)
  } else {
    val ret = ArrayList<Stmt>()
    Pair(
      ret,
      this.withOps(
        this.ops.map { it.uniqueDereferences(vargen, lookup).also { ret.addAll(it.first) }.second }
      ),
    )
  }

object TopCollection : Set<Expr<*>> {

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
  NONE, // do not keep track of any pointer acceses
}

fun <A : Type, O : Type, T : Type> Dereference<A, O, T>.getIte(
  writeTriples: WriteTriples
): Expr<IntType> {
  val list = writeTriples[type] ?: emptyList()
  return list.fold(Int(0) as Expr<IntType>) { elze, (arr, off, value) ->
    IteExpr.of(BoolExprs.And(listOf(Eq(arr, array), Eq(off, offset))), value, elze)
  }
}

fun <S : ExprState> S.patch(writeTriples: WriteTriples): S =
  when (this) {
    is PredState -> PredState.of(preds.map { it.patch(writeTriples) }) as S
    is ExplState -> this
    is UnitState -> this
    is PtrState<*> ->
      (this as PtrState<ExprState>).copy(innerState = innerState.patch(writeTriples)) as S
    else -> error("State $this is not supported")
  }

fun <P : Prec> P.patch(writeTriples: WriteTriples): P =
  when (this) {
    is PredPrec -> PredPrec.of(preds.map { it.patch(writeTriples) }) as P
    is ExplPrec -> this
    is UnitPrec -> this
    else -> error("Prec $this is not supported")
  }

private fun <T : Type> Expr<T>.patch(writeTriples: WriteTriples): Expr<T> =
  when (this) {
    is Dereference<*, *, T> ->
      withUniquenessExpr(getIte(writeTriples)).map { it.patch(writeTriples) }
    else -> map { it.patch(writeTriples) }
  }

fun <P : Prec> P.repatch(): P =
  when (this) {
    is PredPrec -> PredPrec.of(preds.map { it.repatch() }) as P
    is ExplPrec -> this
    is UnitPrec -> this
    else -> error("Prec $this is not supported")
  }

fun <S : ExprState> S.repatch(): S =
  when (this) {
    is PredState -> PredState.of(preds.map(Expr<BoolType>::repatch)) as S
    is ExplState -> this
    is UnitState -> this
    else -> error("State $this is not supported")
  }

private fun <T : Type> Expr<T>.repatch(): Expr<T> =
  when (this) {
    is Dereference<*, *, T> -> withUniquenessExpr(Int(0)).map(Expr<*>::repatch)
    else -> map(Expr<*>::repatch)
  }
