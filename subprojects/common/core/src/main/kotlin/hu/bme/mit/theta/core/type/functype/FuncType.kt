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
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.KSerializer
import kotlinx.serialization.PolymorphicSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/** Represents a function type from ParamType to ResultType. */
@Serializable(with = FuncType.Serializer::class)
@SerialName(FuncType.TYPE_LABEL)
data class FuncType<ParamType : Type, ResultType : Type>(
  val paramType: ParamType,
  val resultType: ResultType,
) : Type {

  companion object {

    internal const val TYPE_LABEL = "Func"

    @JvmStatic
    fun <ParamType : Type, ResultType : Type> of(paramType: ParamType, resultType: ResultType) =
      FuncType(paramType, resultType)
  }

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add(paramType).add(resultType).toString()

  override val domainSize: DomainSize
    get() = throw UnsupportedOperationException()

  object Serializer : KSerializer<FuncType<out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("FuncType") {
        element<String>("paramType")
        element<String>("resultType")
      }

    override fun serialize(encoder: Encoder, value: FuncType<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(
          descriptor,
          0,
          PolymorphicSerializer(Type::class),
          value.paramType,
        )
        encodeSerializableElement(
          descriptor,
          1,
          PolymorphicSerializer(Type::class),
          value.resultType,
        )
      }

    override fun deserialize(decoder: Decoder): FuncType<Type, Type> =
      decoder.decodeStructure(descriptor) {
        var paramType: Type? = null
        var resultType: Type? = null

        while (true) {
          when (val index = decodeElementIndex(descriptor)) {
            0 ->
              paramType =
                decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))
            1 ->
              resultType =
                decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> error("Unexpected index: $index")
          }
        }

        FuncType(
          paramType = paramType ?: error("Missing paramType"),
          resultType = resultType ?: error("Missing resultType"),
        )
      }
  }
}
