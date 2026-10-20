/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.type

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class FuncAppExpr<ParamType : Type, ResultType : Type>
private constructor(val func: Expr<FuncType<ParamType, ResultType>>, val param: Expr<ParamType>) :
  Expr<ResultType> {

  @Transient @Volatile private var hashCode = 0

  override val type: ResultType
    get() = func.type.resultType

  override fun eval(valuation: Valuation): LitExpr<ResultType> =
    // TODO Auto-generated method stub
    throw UnsupportedOperationException("TODO: auto-generated method stub")

  override val arity: Int
    get() = 2

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(func, param)

  override fun withOps(ops: List<Expr<*>>): Expr<ResultType> =
    cast(create<Type, Type>(ops[0], ops[1]), type)

  fun with(
    func: Expr<FuncType<ParamType, ResultType>>,
    param: Expr<ParamType>,
  ): FuncAppExpr<ParamType, ResultType> =
    if (this.func === func && this.param === param) this else of(func, param)

  fun withFunc(func: Expr<FuncType<ParamType, ResultType>>): FuncAppExpr<ParamType, ResultType> =
    with(func, param)

  fun withParam(param: Expr<ParamType>): FuncAppExpr<ParamType, ResultType> = with(func, param)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + func.hashCode()
      result = 31 * result + param.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FuncAppExpr<*, *>
    return func == that.func && param == that.param
  }

  override fun toString(): String = Utils.lispStringBuilder().add(func).body().add(param).toString()

  companion object {
    private const val HASH_SEED = 7951

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(
      func: Expr<FuncType<ParamType, ResultType>>,
      param: Expr<ParamType>,
    ): FuncAppExpr<ParamType, ResultType> = FuncAppExpr(func, param)

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> create(
      func: Expr<*>,
      param: Expr<*>,
    ): FuncAppExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val funcType = func.type as FuncType<ParamType, ResultType>
      return of(cast(func, funcType), cast(param, funcType.paramType))
    }
  }
}
