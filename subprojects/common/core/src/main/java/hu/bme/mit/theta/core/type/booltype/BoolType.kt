package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Boolean type for expressions.
 */
@Serializable
@SerialName(BoolType.TYPE_LABEL)
object BoolType : Equational<BoolType> {

    internal const val TYPE_LABEL = "Bool"
    fun getInstance(): BoolType = this
    override fun toString(): String = TYPE_LABEL

    override fun Eq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): IffExpr =
        BoolExprs.Iff(leftOp, rightOp)

    override fun Neq(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): NeqExpr<BoolType> =
        BoolExprs.Xor(leftOp, rightOp)

    override val domainSize: DomainSize = DomainSize.TWO
}

