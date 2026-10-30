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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

fun XcfaBuilder.getPtrSizeVar(): VarDecl<ArrayType<*, *>> =
  getVars().find { it.wrappedVar.name == "__theta_ptr_size" }!!.wrappedVar
    as VarDecl<ArrayType<*, *>>

fun XcfaBuilder.allocate(parseContext: ParseContext, base: Expr<*>, size: Expr<*>): StmtLabel =
  writeGhost(parseContext, getPtrSizeVar(), base, size)

/**
 * The extent of each flat slot (size plus gap), keyed by its start; 0 for a non-start. Written once
 * per slot and never cleared, so the slots tile the allocated address range even after a `free`.
 * Present only under memsafety with flat addressing.
 */
fun XcfaBuilder.getObjExtentVar(): VarDecl<ArrayType<*, *>>? =
  getVars().find { it.wrappedVar.name == OBJ_EXTENT_VAR }?.wrappedVar as VarDecl<ArrayType<*, *>>?

/** Nonzero at the start of each heap block; the flat-addressing counterpart of the `3k+0` class. */
fun XcfaBuilder.getObjHeapVar(): VarDecl<ArrayType<*, *>>? =
  getVars().find { it.wrappedVar.name == OBJ_HEAP_VAR }?.wrappedVar as VarDecl<ArrayType<*, *>>?

const val OBJ_EXTENT_VAR = "__theta_obj_extent"
const val OBJ_HEAP_VAR = "__theta_obj_heap"

private val GHOST_ARRAYS = setOf("__theta_ptr_size", OBJ_EXTENT_VAR, OBJ_HEAP_VAR)

/** Whether this is the init procedure's zeroing of a memsafety ghost array. */
fun XcfaLabel.isGhostArrayInit(): Boolean =
  this is StmtLabel &&
    stmt is AssignStmt<*> &&
    (stmt as AssignStmt<*>).varDecl.let { it.name in GHOST_ARRAYS && it.type is ArrayType<*, *> } &&
    (stmt as AssignStmt<*>).expr is ArrayLitExpr<*, *>

/** Writes [value] at pointer [index] of a pointer-indexed, Fitsall-valued ghost array. */
fun writeGhost(
  parseContext: ParseContext,
  arr: VarDecl<ArrayType<*, *>>,
  index: Expr<*>,
  value: Expr<*>,
): StmtLabel {
  // Indexed by the pointer type, holding Fitsall: casting the index to Fitsall would make it too
  // wide for the array. Under integer arithmetic both are Int and the casts are skipped.
  val fitsall = Fitsall(null, parseContext)
  val pointerType = CPointer(null, null, parseContext)
  val indexCast = if (pointerType.smtType is IntType) index else pointerType.castTo(index)
  val valueCast = if (fitsall.smtType is IntType) value else fitsall.castTo(value)
  val write = ArrayWriteExpr.create<Type, Type>(arr.ref, indexCast, valueCast)
  return AssignStmtLabel(arr, write)
}

/**
 * Marks the object as no longer live, by giving it size 0.
 *
 * A negative sentinel (-1) would only work if sizes were compared as signed. They are Fitsall-typed
 * and Fitsall is *unsigned*, so under bitvector arithmetic -1 is the largest representable value: a
 * freed object would then look bigger than any other, `free` would not register, and a program that
 * frees everything would still be reported as leaking. Size 0 means "not live" under signed and
 * unsigned semantics alike, and coincides with the array's default value -- so an object that was
 * never allocated is treated the same as a freed one, which is what the checks want anyway.
 */
fun XcfaBuilder.deallocate(parseContext: ParseContext, base: Expr<*>): StmtLabel {
  val type = Fitsall(null, parseContext)
  return allocate(parseContext, base, type.nullValue)
}

fun XcfaBuilder.allocateUnit(parseContext: ParseContext, base: Expr<*>): StmtLabel {
  val type = Fitsall(null, parseContext)
  return allocate(parseContext, base, type.unitValue)
}
