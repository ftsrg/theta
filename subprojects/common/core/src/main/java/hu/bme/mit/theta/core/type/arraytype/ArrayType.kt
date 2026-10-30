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
package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.serialization.ArrayTypeReferenceSerializer
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.EqExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.NeqExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.Equational
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable(with = ArrayTypeReferenceSerializer::class)
@KeepGeneratedSerializer
@SerialName("array")
class ArrayType<IndexType : Type, ElemType : Type>
private constructor(val indexType: IndexType, val elemType: ElemType) :
  Equational<ArrayType<IndexType, ElemType>> {

  @Transient @Volatile private var hashCode = 0

  override fun Eq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): EqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Eq(leftOp, rightOp)

  override fun Neq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): NeqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Neq(leftOp, rightOp)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + indexType.hashCode()
      result = 31 * result + elemType.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null &&
        javaClass == other.javaClass &&
        indexType == (other as ArrayType<*, *>).indexType &&
        elemType == other.elemType)

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add("([$indexType] -> $elemType)").toString()

  override val domainSize: DomainSize
    get() = DomainSize.pow(elemType.domainSize, indexType.domainSize)

  companion object {
    private const val HASH_SEED = 4919
    private const val TYPE_LABEL = "Array"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      indexType: IndexType,
      elemType: ElemType,
    ): ArrayType<IndexType, ElemType> = ArrayType(indexType, elemType)
  }
}
