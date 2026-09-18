/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.passes.FlatMemoryPass
import java.math.BigInteger

/**
 * Whether the cell this dereference reads is `_Atomic` -- accesses to it are, by definition, not
 * data races with anything.
 *
 * A race between two *variables* checks whether the **variable** is atomic (`!v1.globalVar.atomic`,
 * below). An access *through* a dereference touches the cell it points **at**, which is a different
 * question, and `_Atomic` says which is which:
 * ```
 * _Atomic int *p;   // p is an ordinary variable; p[i] is atomic, and cannot be raced on
 * int * _Atomic p;  // p itself is atomic; what it points at is not
 * ```
 *
 * `_Atomic` is a property of the accessed *cell* -- a struct field, an array element, or a pointee
 * -- but the expression that reaches it is a bare `(base, offset)` of literals by analysis time
 * (folded constants, rebuilt exprs, identity-keyed C types all lost). So atomicity is recorded
 * against the object's base id where that id is minted (global layout in the frontend builder,
 * address-taken objects in [ReferenceElimination]) and resolved here by the base id's *value*.
 *
 * A live pointer *variable* (not folded to a base) is still asked its type directly.
 *
 * Nothing found means nothing skipped -- reporting a race is the safe direction.
 */
fun Dereference<*, *, *>.addressesAtomicData(
  globalVars: Collection<XcfaGlobalVar>,
  parseContext: ParseContext,
): Boolean {
  if (parseContext.memoryModel.flatAddressing()) {
    // FlatMemoryPass folded the base into the offset: array is a bare 0 and offset is the flat
    // address objectBase*STRIDE + cell. Decode it back to (base, cell) and ask directly; the
    // multi-model branches below must not run, because their array-based resolution (a RefExpr
    // pointer, or `initValue == array`) would spuriously match the folded 0 and mark a racy access
    // atomic -- missing a real race. When the address is not a compile-time constant we cannot
    // resolve the object, so we answer "not atomic": that keeps the access in the race check
    // (sound; at worst over-reports), never excludes it.
    val flatAddr = offset.asConstantBigInteger() ?: return false
    val stride = BigInteger.valueOf(FlatMemoryPass.FLAT_STRIDE)
    return parseContext.isAtomicObjectCell(flatAddr.divide(stride), flatAddr.mod(stride).toInt())
  }
  // The object being accessed, identified by the base id its dereference resolves to.
  array.resolveObjectBase(parseContext)?.let { base ->
    if (parseContext.isAtomicObjectCell(base, offset.asConstantBigInteger()?.toInt())) return true
  }
  // A live pointer *variable*: its type says what it points at.
  (array as? RefExpr<*>)?.decl?.let { decl ->
    globalVars.firstOrNull { it.wrappedVar == decl }?.let { if (it.pointsToAtomic) return true }
    val pointee =
      try {
        when (val type = CComplexType.getType(array, parseContext)) {
          is CPointer -> type.embeddedType
          is CArray -> type.embeddedType
          else -> null
        }
      } catch (e: Exception) {
        null
      }
    if (pointee?.isAtomic == true) return true
  }
  // An address-taken object, whose pointer has been folded to a bare literal -- its object id. The
  // pointer ReferenceElimination invented for it still holds that id, and remembers what it points
  // at.
  return globalVars.any { it.pointsToAtomic && it.initValue == array }
}

/**
 * The value of a bare integer/bitvector literal, or null when this is not a compile-time constant.
 */
fun Expr<*>.asConstantBigInteger(): BigInteger? =
  when (this) {
    is IntLitExpr -> value
    is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this)
    else -> null
  }

/**
 * The base id of the object this dereference-base expression denotes: a bare literal is that id
 * directly; a nested `(deref parent offset)` reads a subobject's base from its parent's cell, so it
 * resolves through [ParseContext.subObjectBaseAt] (recursively, for `s.a.b.c`).
 */
fun Expr<*>.resolveObjectBase(parseContext: ParseContext): BigInteger? {
  asConstantBigInteger()?.let {
    return it
  }
  if (this is Dereference<*, *, *>) {
    val parent = array.resolveObjectBase(parseContext) ?: return null
    val offsetValue = offset.asConstantBigInteger()?.toInt() ?: return null
    return parseContext.subObjectBaseAt(parent, offsetValue)
  }
  return null
}
