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
package hu.bme.mit.theta.core.type.anytype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Represents an invalid literal expression.
 *
 * @param ExprType The type of the expression
 */
@Serializable(with = InvalidLitExpr.Serializer::class)
@SerialName("InvalidLit")
data class InvalidLitExpr<ExprType : Type>(override val type: ExprType) :
  NullaryExpr<ExprType>(), LitExpr<ExprType> {

  override fun eval(`val`: Valuation): LitExpr<ExprType> = this

  override val isInvalid: Boolean = true

  override fun equals(other: Any?): Boolean = false

  object Serializer : KSerializer<InvalidLitExpr<out Type>> {
    override val descriptor = buildClassSerialDescriptor("InvalidLit") {
      element<Type>("type")
    }
    override fun serialize(encoder: Encoder, value: InvalidLitExpr<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class), value.type)
      }
    override fun deserialize(decoder: Decoder): InvalidLitExpr<out Type> =
      decoder.decodeStructure(descriptor) {
        var type: Type? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> type = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        InvalidLitExpr(
          type = type ?: throw SerializationException("Missing type ")
        )
      }
  }
}
