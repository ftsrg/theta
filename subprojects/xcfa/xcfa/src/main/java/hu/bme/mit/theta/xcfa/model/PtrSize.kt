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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
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

fun XcfaBuilder.allocate(parseContext: ParseContext, base: Expr<*>, size: Expr<*>): StmtLabel {
  // `__theta_ptr_size` maps a pointer base to an object size, so it is *indexed* by the pointer
  // type and *holds* Fitsall. The base must therefore be cast to the pointer type -- casting it to
  // Fitsall (as the size is) makes the index too wide for the array. Under integer arithmetic both
  // are the same unbounded Int and the casts are skipped, which is why this only ever showed up
  // under bitvector arithmetic. Every read of the array (MemsafetyPass) already indexes with a
  // pointer-typed expression.
  val fitsall = Fitsall(null, parseContext)
  val pointerType = CPointer(null, null, parseContext)
  val arr = getPtrSizeVar()
  val baseCast = if (pointerType.smtType is IntType) base else pointerType.castTo(base)
  val sizeCast = if (fitsall.smtType is IntType) size else fitsall.castTo(size)
  val write = ArrayWriteExpr.create<Type, Type>(arr.ref, baseCast, sizeCast)
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
