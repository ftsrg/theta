package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Polymorphic

/**
 * Represents a type that supports division-related operations.
 *
 * @param ExprType The type of expressions this type operates on.
 */
@Polymorphic
interface Divisible<ExprType : Divisible<ExprType>> : Type {

    fun Mod(leftOp: Expr<ExprType>, rightOp: Expr<ExprType>): ModExpr<ExprType>
    fun Rem(leftOp: Expr<ExprType>, rightOp: Expr<ExprType>): RemExpr<ExprType>
}

