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
import hu.bme.mit.theta.core.decl.ParamDecl
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

/** Function literal expression (lambda abstraction) for function types. */
@Serializable(with = FuncLitExpr.Serializer::class)
@SerialName("FuncLit")
data class FuncLitExpr<ParamType : Type, ResultType : Type>(
  val param: ParamDecl<ParamType>,
  val result: Expr<ResultType>,
) : LitExpr<FuncType<ParamType, ResultType>> {

  companion object {

    private const val OPERATOR_LABEL = "func"

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(
      param: ParamDecl<ParamType>,
      result: Expr<ResultType>,
    ) = FuncLitExpr(param, result)
  }

  override val type: FuncType<ParamType, ResultType> = FuncType.of(param.type, result.type)

  override fun eval(`val`: Valuation): LitExpr<FuncType<ParamType, ResultType>> = this

  override val ops: List<Expr<*>> = listOf(result)

  override fun withOps(ops: List<Expr<*>>): FuncLitExpr<ParamType, ResultType> {
    require(ops.size == 1)
    return with(cast(ops[0], result.type))
  }

  fun with(result: Expr<ResultType>): FuncLitExpr<ParamType, ResultType> =
    if (this.result == result) this else of(param, result)

  override fun toString(): String {
    val paramString = "(${param.name} ${param.type})"
    return Utils.lispStringBuilder(OPERATOR_LABEL).body().add(paramString).add(result).toString()
  }

  object Serializer : KSerializer<FuncLitExpr<out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("FuncLit") {
        element<ParamDecl<out Type>>("param")
        element<Expr<out Type>>("result")
      }

    override fun serialize(encoder: Encoder, value: FuncLitExpr<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(
          descriptor,
          0,
          PolymorphicSerializer(ParamDecl::class),
          value.param,
        )
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.result)
      }

    override fun deserialize(decoder: Decoder): FuncLitExpr<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var param: ParamDecl<out Type>? = null
        var result: Expr<out Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 ->
              param =
                decodeSerializableElement(descriptor, 0, PolymorphicSerializer(ParamDecl::class))
            1 ->
              result = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        FuncLitExpr(
          param ?: throw SerializationException("Missing param"),
          result ?: throw SerializationException("Missing result"),
        )
      }
  }
}
