package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.InvalidLitExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(EnumType.TYPE_LABEL)
data class EnumType(
    val name: String,
    private val literals: Map<String, Int>,
) : Equational<EnumType>, Type {

    companion object {

        internal const val TYPE_LABEL = "Enum"
        const val FULLY_QUALIFIED_NAME_SEPARATOR = "."
        @JvmStatic
        fun of(name: String, values: Collection<String>) =
            EnumType(name, values.withIndex().associate { it.value to it.index }.toMap(LinkedHashMap()))

        @JvmStatic
        fun makeLongName(typeName: String, literal: String) = "$typeName$FULLY_QUALIFIED_NAME_SEPARATOR$literal"
        @JvmStatic
        fun makeLongName(type: EnumType, literal: String) = makeLongName(type.name, literal)
        @JvmStatic
        fun getShortName(longName: String): String =
            if (FULLY_QUALIFIED_NAME_SEPARATOR !in longName) longName
            else longName.substring(
                longName.indexOf(FULLY_QUALIFIED_NAME_SEPARATOR) + FULLY_QUALIFIED_NAME_SEPARATOR.length
            )
    }

    override val domainSize: DomainSize get() = DomainSize.of(literals.size.toLong())

    override fun Eq(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EqExpr<EnumType> = EnumEqExpr.of(leftOp, rightOp)
    override fun Neq(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): NeqExpr<EnumType> =
        EnumNeqExpr.of(leftOp, rightOp)

    val values: Set<String> get() = literals.keys
    val longValues: Set<String> get() = literals.keys.map { makeLongName(this, it) }.toSet()

    fun getIntValue(literal: EnumLitExpr): Int = getIntValue(literal.value)
    fun getIntValue(literal: String): Int = literals[literal]
        ?: throw IllegalArgumentException("Enum type $name does not contain literal '$literal'")

    fun litFromShortName(shortName: String): LitExpr<EnumType> =
        try {
            EnumLitExpr.of(this, shortName)
        } catch (e: Exception) {
            throw RuntimeException("$shortName is not valid for type $name", e)
        }

    fun litFromLongName(longName: String): LitExpr<EnumType> {
        if (FULLY_QUALIFIED_NAME_SEPARATOR !in longName)
            throw RuntimeException("$longName is an invalid enum longname")
        val parts = longName.split(FULLY_QUALIFIED_NAME_SEPARATOR)
        val type = parts[0]
        require(name == type) { "$type does not belong to type $name" }
        return litFromShortName(parts[1])
    }

    fun litFromIntValue(value: Int): LitExpr<EnumType> =
        literals.entries.find { it.value == value }?.let { EnumLitExpr.of(this, it.key) }
            ?: InvalidLitExpr(this)

    override fun toString(): String = "EnumType{$name}"
}
