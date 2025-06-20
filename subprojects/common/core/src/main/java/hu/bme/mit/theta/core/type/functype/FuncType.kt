package hu.bme.mit.theta.core.type.functype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Represents a function type from ParamType to ResultType.
 */
@Serializable
@SerialName(FuncType.TYPE_LABEL)
data class FuncType<ParamType : Type, ResultType : Type>(
    val paramType: ParamType,
    val resultType: ResultType
) : Type {

    companion object {

        internal const val TYPE_LABEL = "Func"

        @JvmStatic
        fun <ParamType : Type, ResultType : Type> of(paramType: ParamType, resultType: ResultType) =
            FuncType(paramType, resultType)
    }

    override fun toString(): String = Utils.lispStringBuilder(TYPE_LABEL).add(paramType).add(resultType).toString()
    override val domainSize: DomainSize get() = throw UnsupportedOperationException()
}

