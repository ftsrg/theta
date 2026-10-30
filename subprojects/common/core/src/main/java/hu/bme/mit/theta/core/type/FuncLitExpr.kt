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

import com.google.common.base.Preconditions.checkArgument
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class FuncLitExpr<ParamType : Type, ResultType : Type>
private constructor(val param: ParamDecl<ParamType>, val result: Expr<ResultType>) :
  LitExpr<FuncType<ParamType, ResultType>> {

  @Transient @Volatile private var hashCode = 0

  override val type: FuncType<ParamType, ResultType>
    get() = FuncType.of(param.type, result.type)

  override fun eval(valuation: Valuation): LitExpr<FuncType<ParamType, ResultType>> = this

  override val arity: Int
    get() = 1

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(result)

  override fun withOps(ops: List<Expr<*>>): Expr<FuncType<ParamType, ResultType>> {
    checkArgument(ops.size == 1)
    return with(TypeUtils.cast(ops[0], result.type))
  }

  fun with(result: Expr<ResultType>): FuncLitExpr<ParamType, ResultType> =
    if (this.result === result) this else of(param, result)

  override fun hashCode(): Int {
    var tmp = hashCode
    if (tmp == 0) {
      tmp = HASH_SEED
      tmp = 31 * tmp + param.hashCode()
      tmp = 31 * tmp + result.hashCode()
      hashCode = tmp
    }
    return tmp
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as FuncLitExpr<*, *>
    return param == that.param && result == that.result
  }

  override fun toString(): String {
    val paramString = String.format("(%s %s)", param.name, param.type)
    return Utils.lispStringBuilder(OPERATOR_LABEL).body().add(paramString).add(result).toString()
  }

  companion object {
    private const val HASH_SEED = 53
    private const val OPERATOR_LABEL = "func"

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(
      param: ParamDecl<ParamType>,
      result: Expr<ResultType>,
    ): FuncLitExpr<ParamType, ResultType> = FuncLitExpr(param, result)
  }
}
