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

package hu.bme.mit.theta.core.type.bvtype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr

@Suppress("FunctionName")
object BvExprs {

    @JvmStatic
    fun BvType(size: Int) = BvType.of(size, null)

    @JvmStatic
    fun BvType(size: Int, signedness: Boolean?) = BvType.of(size, signedness)

    @JvmStatic
    fun Bv(value: BooleanArray) = BvLitExpr(value, null)

    @JvmStatic
    fun Bv(value: BooleanArray, signedness: Boolean?) = BvLitExpr(value, signedness)

    @JvmStatic
    fun Concat(ops: Iterable<Expr<BvType>>) = BvConcatExpr.of(ops)

    @JvmStatic
    fun Extract(bitvec: Expr<BvType>, from: IntLitExpr, until: IntLitExpr) = BvExtractExpr(bitvec, from, until)

    @JvmStatic
    fun ZExt(bitvec: Expr<BvType>, extendType: BvType) = BvZExtExpr(bitvec, extendType)

    @JvmStatic
    fun SExt(bitvec: Expr<BvType>, extendType: BvType) = BvSExtExpr(bitvec, extendType)

    @JvmStatic
    fun Add(ops: Iterable<Expr<BvType>>) = BvAddExpr.of(ops)

    @JvmStatic
    fun Sub(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSubExpr(leftOp, rightOp)

    @JvmStatic
    fun Pos(op: Expr<BvType>) = BvPosExpr(op)

    @JvmStatic
    fun Neg(op: Expr<BvType>) = BvNegExpr(op)

    @JvmStatic
    fun Mul(ops: Iterable<Expr<BvType>>) = BvMulExpr.of(ops)

    @JvmStatic
    fun UDiv(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvUDivExpr(leftOp, rightOp)

    @JvmStatic
    fun SDiv(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSDivExpr(leftOp, rightOp)

    @JvmStatic
    fun SMod(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSModExpr(leftOp, rightOp)

    @JvmStatic
    fun URem(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvURemExpr(leftOp, rightOp)

    @JvmStatic
    fun SRem(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSRemExpr(leftOp, rightOp)

    @JvmStatic
    fun Or(ops: Iterable<Expr<BvType>>) = BvOrExpr.of(ops)

    @JvmStatic
    fun And(ops: Iterable<Expr<BvType>>) = BvAndExpr.of(ops)

    @JvmStatic
    fun Xor(ops: Iterable<Expr<BvType>>) = BvXorExpr.of(ops)

    @JvmStatic
    fun Not(op: Expr<BvType>) = BvNotExpr(op)

    @JvmStatic
    fun ShiftLeft(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvShiftLeftExpr(leftOp, rightOp)

    @JvmStatic
    fun ArithShiftRight(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvArithShiftRightExpr(leftOp, rightOp)

    @JvmStatic
    fun LogicShiftRight(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvLogicShiftRightExpr(leftOp, rightOp)

    @JvmStatic
    fun RotateLeft(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvRotateLeftExpr(leftOp, rightOp)

    @JvmStatic
    fun RotateRight(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvRotateRightExpr(leftOp, rightOp)

    @JvmStatic
    fun Eq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvEqExpr(leftOp, rightOp)

    @JvmStatic
    fun Neq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvNeqExpr(leftOp, rightOp)

    @JvmStatic
    fun ULt(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvULtExpr(leftOp, rightOp)

    @JvmStatic
    fun ULeq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvULeqExpr(leftOp, rightOp)

    @JvmStatic
    fun UGt(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvUGtExpr(leftOp, rightOp)

    @JvmStatic
    fun UGeq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvUGeqExpr(leftOp, rightOp)

    @JvmStatic
    fun SLt(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSLtExpr(leftOp, rightOp)

    @JvmStatic
    fun SLeq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSLeqExpr(leftOp, rightOp)

    @JvmStatic
    fun SGt(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSGtExpr(leftOp, rightOp)

    @JvmStatic
    fun SGeq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvSGeqExpr(leftOp, rightOp)
}
