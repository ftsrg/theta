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
package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Equality expression for array types. */
@Serializable
@SerialName("ArrayEqExpr")
data class ArrayEqExpr<IndexType : Type, ElemType : Type>(
  override val leftOp: Expr<ArrayType<IndexType, ElemType>>,
  override val rightOp: Expr<ArrayType<IndexType, ElemType>>,
) : EqExpr<ArrayType<IndexType, ElemType>>() {

  companion object {

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      leftOp: Expr<ArrayType<IndexType, ElemType>>,
      rightOp: Expr<ArrayType<IndexType, ElemType>>,
    ) = ArrayEqExpr(leftOp, rightOp)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      leftOp: Expr<*>,
      rightOp: Expr<*>,
    ): ArrayEqExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val arrayType = leftOp.type as ArrayType<IndexType, ElemType>
      val newLeftOp = cast(leftOp, arrayType)
      val newRightOp = cast(rightOp, arrayType)
      return of(newLeftOp, newRightOp)
    }
  }

  override fun eval(`val`: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

  override fun new(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): ArrayEqExpr<IndexType, ElemType> = of(leftOp, rightOp)

  override fun toString(): String = super.toString()
}
