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
package hu.bme.mit.theta.core.type.anytype

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Factory and utility methods for any-type expressions.
 */
@Suppress("FunctionName")
object Exprs {
    @JvmStatic
    fun <DeclType : Type> Ref(decl: Decl<DeclType>): RefExpr<DeclType> =
        RefExpr(decl)

    @JvmStatic
    fun <ExprType : Type> Ite(
        cond: Expr<BoolType>,
        then: Expr<ExprType>,
        elze: Expr<ExprType>
    ): IteExpr<ExprType> =
        IteExpr(cond, then, elze)

    @JvmStatic
    fun <ExprType : Type> Prime(op: Expr<ExprType>): PrimeExpr<ExprType> =
        PrimeExpr(op)

    @JvmStatic
    fun <ArrType : Type, OffsetType : Type, ExprType : Type> Dereference(
        arr: Expr<ArrType>,
        offset: Expr<OffsetType>,
        type: ExprType
    ): Dereference<ArrType, OffsetType, ExprType> =
        Dereference(arr, offset, type)

    @JvmStatic
    fun <ArrType : Type, ExprType : Type> Reference(
        expr: Expr<ExprType>,
        type: ArrType
    ): Reference<ArrType, ExprType> =
        Reference(expr, type)

    // Convenience methods
    @JvmStatic
    fun <ExprType : Type> Prime(op: Expr<ExprType>, i: Int): Expr<ExprType> {
        require(i >= 0)
        return when (i) {
            0 -> op
            1 -> Prime(op)
            else -> Prime(Prime(op, i - 1))
        }
    }
}
