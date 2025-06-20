package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.Expr

/**
 * Factory and utility methods for boolean expressions.
 */
@Suppress("FunctionName")
object BoolExprs {
    fun Bool() = BoolType
    fun Bool(value: Boolean) = BoolLitExpr.of(value)
    fun True() = TrueExpr
    fun False() = FalseExpr
    fun Not(op: Expr<BoolType>) = NotExpr(op)
    fun Imply(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = ImplyExpr(leftOp, rightOp)
    fun Iff(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = IffExpr(leftOp, rightOp)
    fun Xor(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = XorExpr(leftOp, rightOp)
    fun And(ops: Iterable<Expr<BoolType>>) = AndExpr.of(ops)
    fun Or(ops: Iterable<Expr<BoolType>>) = OrExpr.of(ops)
    fun Forall(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) = ForallExpr.of(paramDecls, op)
    fun Exists(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) = ExistsExpr.of(paramDecls, op)
    // Convenience methods
    fun And(vararg ops: Expr<BoolType>) = AndExpr.of(ops.asList())
    fun Or(vararg ops: Expr<BoolType>) = OrExpr.of(ops.asList())
}

