/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/** Function application expression for function types. */
@Serializable(with = FuncAppExpr.Serializer::class)
@SerialName("FuncApp")
data class FuncAppExpr<ParamType : Type, ResultType : Type>(
  val func: Expr<FuncType<ParamType, ResultType>>,
  val param: Expr<ParamType>,
) : Expr<ResultType> {

  companion object {

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(
      func: Expr<FuncType<ParamType, ResultType>>,
      param: Expr<ParamType>,
    ) = FuncAppExpr(func, param)

    @Suppress("UNCHECKED_CAST")
    @JvmStatic
    fun <ParamType : Type, ResultType : Type> create(
      func: Expr<*>,
      param: Expr<*>,
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
    param: Expr<ParamType>,
  ): FuncAppExpr<ParamType, ResultType> =
    if (this.func == func && this.param == param) this else of(func, param)

  fun withFunc(func: Expr<FuncType<ParamType, ResultType>>): FuncAppExpr<ParamType, ResultType> =
    with(func, param)

  fun withParam(param: Expr<ParamType>): FuncAppExpr<ParamType, ResultType> = with(func, param)

  override fun toString(): String = Utils.lispStringBuilder().add(func).body().add(param).toString()

  object Serializer : KSerializer<FuncAppExpr<out Type, out Type>> {
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("FuncApp") {
      element<Expr<out Type>>("func")
      element<Expr<out Type>>("param")
    }
    override fun serialize(encoder: Encoder, value: FuncAppExpr<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.func)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.param)
      }
    override fun deserialize(decoder: Decoder): FuncAppExpr<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var func: Expr<FuncType<Type, Type>>? = null
        var param: Expr<Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> func = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class)) as Expr<FuncType<Type, Type>>
            1 -> param = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class)) as Expr<Type>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        FuncAppExpr(
          func ?: throw SerializationException("Missing func"),
          param ?: throw SerializationException("Missing param")
        )
      }
  }
}
