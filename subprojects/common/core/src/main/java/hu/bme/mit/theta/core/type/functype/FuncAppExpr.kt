package hu.bme.mit.theta.core.type.functype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Function application expression for function types.
 */
@Serializable
@SerialName("FuncAppExpr")
data class FuncAppExpr<ParamType : Type, ResultType : Type>(
    val func: Expr<FuncType<ParamType, ResultType>>,
    val param: Expr<ParamType>
) : Expr<ResultType> {

    companion object {

        @JvmStatic
        fun <ParamType : Type, ResultType : Type> of(
            func: Expr<FuncType<ParamType, ResultType>>,
            param: Expr<ParamType>
        ) = FuncAppExpr(func, param)

        @Suppress("UNCHECKED_CAST")
        @JvmStatic
        fun <ParamType : Type, ResultType : Type> create(
            func: Expr<*>,
            param: Expr<*>
        ): FuncAppExpr<ParamType, ResultType> {
            val funcType = func.type as FuncType<ParamType, ResultType>
            val newFunc = cast(func, funcType)
            val newParam = cast(param, funcType.paramType)
            return of(newFunc, newParam)
        }
    }

    override val type: ResultType = func.type.resultType
    override fun eval(`val`: Valuation): LitExpr<ResultType> = throw UnsupportedOperationException()
    override val ops: List<Expr<*>> = listOf(func, param)
    override fun withOps(ops: List<Expr<*>>): Expr<ResultType> {
        require(ops.size == 2)
        return cast(create<ParamType, ResultType>(ops[0], ops[1]), type)
    }

    fun with(
        func: Expr<FuncType<ParamType, ResultType>>,
        param: Expr<ParamType>
    ): FuncAppExpr<ParamType, ResultType> =
        if (this.func == func && this.param == param) this else of(func, param)

    fun withFunc(func: Expr<FuncType<ParamType, ResultType>>): FuncAppExpr<ParamType, ResultType> =
        with(func, param)

    fun withParam(param: Expr<ParamType>): FuncAppExpr<ParamType, ResultType> =
        with(func, param)

    override fun toString(): String =
        Utils.lispStringBuilder().add(func).body().add(param).toString()
}

