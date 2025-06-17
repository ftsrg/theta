package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Polymorphic

/**
 * Represents a type that supports multiplication and division operations.
 */
@Polymorphic
interface Multiplicative<ExprType : Multiplicative<ExprType>> : Type {
    fun Mul(ops: Iterable<Expr<ExprType>>): MulExpr<ExprType>
    fun Div(leftOp: Expr<ExprType>, rightOp: Expr<ExprType>): DivExpr<ExprType>
}

