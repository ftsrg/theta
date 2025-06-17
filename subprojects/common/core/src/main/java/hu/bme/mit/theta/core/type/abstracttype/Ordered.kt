package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Polymorphic

/**
 * Represents a type that supports ordering and comparison operations.
 */
@Polymorphic
interface Ordered<OpType : Ordered<OpType>> : Type {
    fun Lt(leftOp: Expr<OpType>, rightOp: Expr<OpType>): LtExpr<OpType>
    fun Leq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): LeqExpr<OpType>
    fun Gt(leftOp: Expr<OpType>, rightOp: Expr<OpType>): GtExpr<OpType>
    fun Geq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): GeqExpr<OpType>
}

