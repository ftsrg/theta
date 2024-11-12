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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.AssignStmtLabel

fun XcfaBuilder.getPtrSizeVar(): VarDecl<ArrayType<*, *>> =
  getVars().find { it.wrappedVar.name == "__theta_ptr_size" }!!.wrappedVar
    as VarDecl<ArrayType<*, *>>

fun XcfaBuilder.allocate(parseContext: ParseContext, base: Expr<*>, size: Expr<*>): StmtLabel {
  val type = Fitsall(null, parseContext)
  val arr = getPtrSizeVar()
  val baseCast = if (type.smtType is IntType) base else type.castTo(base)
  val sizeCast = if (type.smtType is IntType) size else type.castTo(size)
  val write = ArrayWriteExpr.create<Type, Type>(arr.ref, baseCast, sizeCast)
  return AssignStmtLabel(arr, write)
}

fun XcfaBuilder.allocateUnit(parseContext: ParseContext, base: Expr<*>): StmtLabel {
  val type = Fitsall(null, parseContext)
  return allocate(parseContext, base, type.unitValue)
}
