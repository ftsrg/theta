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
package hu.bme.mit.theta.core.type.functype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.serialization.FuncTypeReferenceSerializer
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable(with = FuncTypeReferenceSerializer::class)
@KeepGeneratedSerializer
@SerialName("func")
class FuncType<ParamType : Type, ResultType : Type>
private constructor(val paramType: ParamType, val resultType: ResultType) : Type {

  @Transient @Volatile private var hashCode = 0

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + paramType.hashCode()
      result = 31 * result + resultType.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null &&
        javaClass == other.javaClass &&
        paramType == (other as FuncType<*, *>).paramType &&
        resultType == other.resultType)

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add(paramType).add(resultType).toString()

  override val domainSize: DomainSize
    get() = throw UnsupportedOperationException()

  companion object {
    private const val HASH_SEED = 3931
    private const val TYPE_LABEL = "Func"

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(
      paramType: ParamType,
      resultType: ResultType,
    ): FuncType<ParamType, ResultType> = FuncType(paramType, resultType)
  }
}
