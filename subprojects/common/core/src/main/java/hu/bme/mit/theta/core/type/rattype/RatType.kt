
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(RatType.TYPE_LABEL)
object RatType : Additive<RatType>, Multiplicative<RatType>, Equational<RatType>, Ordered<RatType>, Type {
    internal const val TYPE_LABEL = "Rat"
    @JvmStatic
    fun getInstance(): RatType = this
    override fun toString(): String = TYPE_LABEL

    override fun Add(ops: Iterable<Expr<RatType>>) = RatAddExpr.of(ops)
    override fun Sub(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatSubExpr(leftOp, rightOp)
    override fun Pos(op: Expr<RatType>) = RatPosExpr(op)
    override fun Neg(op: Expr<RatType>) = RatNegExpr(op)
    override fun Mul(ops: Iterable<Expr<RatType>>) = RatMulExpr.of(ops)
    override fun Div(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatDivExpr(leftOp, rightOp)
    override fun Eq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatEqExpr(leftOp, rightOp)
    override fun Neq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatNeqExpr(leftOp, rightOp)
    override fun Lt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLtExpr(leftOp, rightOp)
    override fun Leq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLeqExpr(leftOp, rightOp)
    override fun Gt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGtExpr(leftOp, rightOp)
    override fun Geq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGeqExpr(leftOp, rightOp)

    override val domainSize: DomainSize = DomainSize.INFINITY
}
