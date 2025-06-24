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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type

/** Factory and utility methods for array-type expressions. */
@Suppress("FunctionName")
object ArrayExprs {
  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Array(
    indexType: IndexType,
    elemType: ElemType,
  ): ArrayType<IndexType, ElemType> = ArrayType(indexType, elemType)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Array(
    elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
    elseElem: Expr<ElemType>,
    type: ArrayType<IndexType, ElemType>,
  ): ArrayLitExpr<IndexType, ElemType> = ArrayLitExpr.of(elements, elseElem, type)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> ArrayInit(
    elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
    elseElem: Expr<ElemType>,
    type: ArrayType<IndexType, ElemType>,
  ): ArrayInitExpr<IndexType, ElemType> = ArrayInitExpr(elements, elseElem, type)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Read(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
  ): ArrayReadExpr<IndexType, ElemType> = ArrayReadExpr(array, index)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Write(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
    elem: Expr<ElemType>,
  ): ArrayWriteExpr<IndexType, ElemType> = ArrayWriteExpr(array, index, elem)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Eq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): ArrayEqExpr<IndexType, ElemType> = ArrayEqExpr(leftOp, rightOp)

  @JvmStatic
  fun <IndexType : Type, ElemType : Type> Neq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): ArrayNeqExpr<IndexType, ElemType> = ArrayNeqExpr(leftOp, rightOp)
}
