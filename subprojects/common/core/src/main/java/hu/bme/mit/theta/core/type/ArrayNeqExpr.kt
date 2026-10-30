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
package hu.bme.mit.theta.core.type

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
class ArrayNeqExpr<IndexType : Type, ElemType : Type>
private constructor(
  override val leftOp: Expr<ArrayType<IndexType, ElemType>>,
  override val rightOp: Expr<ArrayType<IndexType, ElemType>>,
) : NeqExpr<ArrayType<IndexType, ElemType>>() {

  override val type: BoolType
    get() = Bool()

  override fun eval(valuation: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

  override fun with(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): ArrayNeqExpr<IndexType, ElemType> =
    if (leftOp === this.leftOp && rightOp === this.rightOp) this else of(leftOp, rightOp)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 5233
    private const val OPERATOR_LABEL = "/="

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      leftOp: Expr<ArrayType<IndexType, ElemType>>,
      rightOp: Expr<ArrayType<IndexType, ElemType>>,
    ): ArrayNeqExpr<IndexType, ElemType> = ArrayNeqExpr(leftOp, rightOp)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      leftOp: Expr<*>,
      rightOp: Expr<*>,
    ): ArrayNeqExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val arrayType = leftOp.type as ArrayType<IndexType, ElemType>
      return of(cast(leftOp, arrayType), cast(rightOp, arrayType))
    }
  }
}
