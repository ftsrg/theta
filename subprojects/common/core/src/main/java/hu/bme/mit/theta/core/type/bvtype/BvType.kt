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

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode.Companion.defaultRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import java.math.BigInteger


@Serializable
@SerialName(BvType.TYPE_LABEL)
data class BvType(
    val size: Int,
    val signed: Boolean?,
) : Additive<BvType>, Multiplicative<BvType>, Divisible<BvType>, Equational<BvType>, Ordered<BvType>, Castable<BvType> {

    init {
        require(size > 0) { "Bitvector size must be positive" }
    }

    companion object {

        internal const val TYPE_LABEL = "Bv"

        @JvmStatic
        fun of(size: Int): BvType = BvType(size, null)

        @JvmStatic
        fun of(size: Int, signed: Boolean?): BvType = BvType(size, signed)
    }

    fun withSize(size: Int): BvType = BvType(size, signed)

    fun isSigned(): Boolean = signed ?: error("Signedness is not specified")

    override fun Eq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvEqExpr(leftOp, rightOp)
    override fun Neq(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvNeqExpr(leftOp, rightOp)
    override fun Add(ops: Iterable<Expr<BvType>>) = BvExprs.Add(ops)
    override fun Sub(leftOp: Expr<BvType>, rightOp: Expr<BvType>) = BvExprs.Sub(leftOp, rightOp)
    override fun Pos(op: Expr<BvType>) = BvExprs.Pos(op)
    override fun Neg(op: Expr<BvType>) = BvExprs.Neg(op)
    override fun <TargetType : Type> Cast(op: Expr<BvType>, type: TargetType): Expr<TargetType> {
        if (type is FpType && signed != null) {
            @Suppress("UNCHECKED_CAST")
            return FromBv(defaultRoundingMode, op, type as FpType, signed) as Expr<TargetType>
        }
        throw ClassCastException("Bv cannot be cast to $type")
    }

    override fun Mod(leftOp: Expr<BvType>, rightOp: Expr<BvType>): ModExpr<BvType> {
        check(signed != null && signed) { "Signed BvType required for Mod" }
        return BvExprs.SMod(leftOp, rightOp)
    }

    override fun Rem(leftOp: Expr<BvType>, rightOp: Expr<BvType>): RemExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SRem(leftOp, rightOp) else BvExprs.URem(leftOp, rightOp)
    }

    override fun Mul(ops: Iterable<Expr<BvType>>) = BvExprs.Mul(ops)
    override fun Div(leftOp: Expr<BvType>, rightOp: Expr<BvType>): DivExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SDiv(leftOp, rightOp) else BvExprs.UDiv(leftOp, rightOp)
    }

    override fun Lt(leftOp: Expr<BvType>, rightOp: Expr<BvType>): LtExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SLt(leftOp, rightOp) else BvExprs.ULt(leftOp, rightOp)
    }

    override fun Leq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): LeqExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SLeq(leftOp, rightOp) else BvExprs.ULeq(leftOp, rightOp)
    }

    override fun Gt(leftOp: Expr<BvType>, rightOp: Expr<BvType>): GtExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SGt(leftOp, rightOp) else BvExprs.UGt(leftOp, rightOp)
    }

    override fun Geq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): GeqExpr<BvType> {
        check(signed != null) { "Neutral BvType cannot be used here" }
        return if (signed) BvExprs.SGeq(leftOp, rightOp) else BvExprs.UGeq(leftOp, rightOp)
    }

    override val domainSize: DomainSize get() = DomainSize.of(BigInteger.TWO.pow(size))

    override fun toString(): String = Utils.lispStringBuilder(TYPE_LABEL).add(size).toString()
}

