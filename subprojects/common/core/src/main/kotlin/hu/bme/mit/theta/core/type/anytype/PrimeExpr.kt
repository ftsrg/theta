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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.UnaryExpr
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Represents a prime expression (next state).
 *
 * @param ExprType The type of the expression
 */
@Serializable(with = PrimeExpr.Serializer::class)
@SerialName("Prime")
data class PrimeExpr<ExprType : Type>(override val op: Expr<ExprType>) :
  UnaryExpr<ExprType, ExprType>() {

  companion object {

    private const val OPERATOR_LABEL = "prime"

    @JvmStatic fun <T : Type> of(op: Expr<T>): PrimeExpr<T> = PrimeExpr(op)
  }

  override val type: ExprType = op.type

  override fun eval(`val`: Valuation): LitExpr<ExprType> {
    throw UnsupportedOperationException("Prime expressions cannot be evaluated")
  }

  override fun new(op: Expr<ExprType>): PrimeExpr<ExprType> = of(op)

  override val operatorLabel: String = OPERATOR_LABEL

  object Serializer : KSerializer<PrimeExpr<out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("Prime") { element<Expr<out Type>>("op") }

    override fun serialize(encoder: Encoder, value: PrimeExpr<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.op)
      }

    override fun deserialize(decoder: Decoder): PrimeExpr<out Type> =
      decoder.decodeStructure(descriptor) {
        var op: Expr<out Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> op = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        PrimeExpr(op = op ?: throw SerializationException("Missing op "))
      }
  }
}
