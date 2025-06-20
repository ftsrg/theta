package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Abstract base class for quantified boolean expressions (forall, exists).
 */
@Serializable
sealed class QuantifiedExpr : Expr<BoolType> {

    abstract val paramDecls: List<ParamDecl<*>>
    abstract val op: Expr<BoolType>

    override val type: BoolType = Bool()
    override val ops: List<Expr<*>> get() = listOf(op)
    override fun withOps(ops: List<Expr<*>>): Expr<BoolType> {
        require(ops.size == 1) { "QuantifiedExpr expects exactly one operand." }
        return with(cast(ops[0], Bool()))
    }

    override fun eval(`val`: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

    override fun toString(): String {
        val paramString = paramDecls.joinToString(" ", prefix = "(", postfix = ")") { "(${it.name} ${it.type})" }
        return Utils.lispStringBuilder(operatorLabel).body().add(paramString).add(op).toString()
    }

    abstract fun with(op: Expr<BoolType>): QuantifiedExpr
    protected abstract val operatorLabel: String
}

/**
 * Existential quantifier expression for boolean type.
 */
@Serializable
@SerialName(ExistsExpr.OPERATOR_LABEL)
data class ExistsExpr(
    override val paramDecls: List<ParamDecl<*>>,
    override val op: Expr<BoolType>
) : QuantifiedExpr() {

    companion object {

        internal const val OPERATOR_LABEL = "exists"
        fun of(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) =
            ExistsExpr(paramDecls.toList(), op)

        fun create(paramDecls: Iterable<ParamDecl<*>>, op: Expr<*>) =
            ExistsExpr(paramDecls.toList(), cast(op, Bool()))
    }

    override fun with(op: Expr<BoolType>): ExistsExpr =
        if (op == this.op) this else ExistsExpr(paramDecls, op)

    override val operatorLabel: String = OPERATOR_LABEL
}

/**
 * Universal quantifier expression for boolean type.
 */
@Serializable
@SerialName(ForallExpr.OPERATOR_LABEL)
data class ForallExpr(
    override val paramDecls: List<ParamDecl<*>>,
    override val op: Expr<BoolType>
) : QuantifiedExpr() {

    companion object {

        internal const val OPERATOR_LABEL = "forall"
        fun of(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) =
            ForallExpr(paramDecls.toList(), op)

        fun create(paramDecls: Iterable<ParamDecl<*>>, op: Expr<*>) =
            ForallExpr(paramDecls.toList(), cast(op, Bool()))
    }

    override fun with(op: Expr<BoolType>): ForallExpr =
        if (op == this.op) this else ForallExpr(paramDecls, op)

    override val operatorLabel: String = OPERATOR_LABEL
}

