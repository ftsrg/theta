package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Abstract base class for boolean literal expressions.
 */
@Serializable
sealed class BoolLitExpr : NullaryExpr<BoolType>(), LitExpr<BoolType> {

    abstract val value: Boolean

    override val type: BoolType = Bool()

    override fun eval(`val`: Valuation): BoolLitExpr = this

    companion object {
        @JvmStatic
        fun of(value: Boolean): BoolLitExpr = if (value) TrueExpr else FalseExpr
    }
}

@Serializable
@SerialName("False")
object FalseExpr : BoolLitExpr() {

    @JvmStatic
    fun getInstance(): FalseExpr = this
    override val value: Boolean = false
    override fun toString(): String = "false"
}

@Serializable
@SerialName("True")
object TrueExpr : BoolLitExpr() {

    @JvmStatic
    fun getInstance(): TrueExpr = this
    override val value: Boolean = true
    override fun toString(): String = "true"
}