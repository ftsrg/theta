package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.type.Expr

/**
 * Utility methods for smart construction and simplification of boolean expressions.
 */
@Suppress("FunctionName")
object SmartBoolExprs {
    fun Not(op: Expr<BoolType>): Expr<BoolType> = when (op) {
        BoolExprs.True() -> BoolExprs.False()
        BoolExprs.False() -> BoolExprs.True()
        is NotExpr -> op.op
        else -> BoolExprs.Not(op)
    }

    fun Imply(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): Expr<BoolType> = when {
        leftOp == BoolExprs.False() -> BoolExprs.True()
        leftOp == BoolExprs.True() -> rightOp
        rightOp == BoolExprs.False() -> Not(leftOp)
        rightOp == BoolExprs.True() -> BoolExprs.True()
        else -> BoolExprs.Imply(leftOp, rightOp)
    }

    fun And(ops: Collection<Expr<BoolType>>): Expr<BoolType> {
        if (ops.isEmpty()) return BoolExprs.True()
        if (BoolExprs.False() in ops) return BoolExprs.False()
        val filteredOps = ops.filter { it != BoolExprs.True() }
        return when (filteredOps.size) {
            0 -> BoolExprs.True()
            1 -> filteredOps.single()
            else -> BoolExprs.And(filteredOps)
        }
    }

    fun Or(ops: Collection<Expr<BoolType>>): Expr<BoolType> {
        if (ops.isEmpty()) return BoolExprs.False()
        if (BoolExprs.True() in ops) return BoolExprs.True()
        val filteredOps = ops.filter { it != BoolExprs.False() }
        return when (filteredOps.size) {
            0 -> BoolExprs.False()
            1 -> filteredOps.single()
            else -> BoolExprs.Or(filteredOps)
        }
    }

    // Convenience methods
    fun And(vararg ops: Expr<BoolType>) = And(ops.toList())
    fun Or(vararg ops: Expr<BoolType>) = Or(ops.toList())
}

