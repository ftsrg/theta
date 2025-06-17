package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Polymorphic

/**
 * Represents a type that supports equational operations.
 *
 * @param OpType The type of the operands, which must also be equational.
 */
@Polymorphic
interface Equational<OpType : Equational<OpType>> : Type {

    fun Eq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): EqExpr<OpType>
    fun Neq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): NeqExpr<OpType>
}
