package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("EnumLitExpr")
data class EnumLitExpr(
    override val type: EnumType,
    val value: String
) : NullaryExpr<EnumType>(), LitExpr<EnumType> {

    companion object {

        fun of(type: EnumType, literalName: String): EnumLitExpr {
            val value = EnumType.getShortName(literalName)
            require(value in type.values) { "Invalid value $value for type ${type.name}" }
            return EnumLitExpr(type, value)
        }

        fun eq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
            Bool(l.type == r.type && l.value == r.value)

        fun neq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
            Bool(l.type != r.type || l.value != r.value)
    }

    override fun eval(`val`: Valuation): LitExpr<EnumType> = this
    override fun toString(): String = EnumType.makeLongName(type, value)
}

