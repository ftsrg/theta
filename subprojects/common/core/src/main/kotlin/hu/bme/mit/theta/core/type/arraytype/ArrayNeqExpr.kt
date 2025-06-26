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
package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/** Not-equal expression for array types. */
@Serializable(with = ArrayNeqExpr.Serializer::class)
@SerialName("ArrayNeq")
data class ArrayNeqExpr<IndexType : Type, ElemType : Type>(
  override val leftOp: Expr<ArrayType<IndexType, ElemType>>,
  override val rightOp: Expr<ArrayType<IndexType, ElemType>>,
) : NeqExpr<ArrayType<IndexType, ElemType>>() {

  companion object {
    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      leftOp: Expr<ArrayType<IndexType, ElemType>>,
      rightOp: Expr<ArrayType<IndexType, ElemType>>,
    ) = ArrayNeqExpr(leftOp, rightOp)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      leftOp: Expr<*>,
      rightOp: Expr<*>,
    ): ArrayNeqExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val arrayType = leftOp.type as ArrayType<IndexType, ElemType>
      val newLeftOp = cast(leftOp, arrayType)
      val newRightOp = cast(rightOp, arrayType)
      return of(newLeftOp, newRightOp)
    }
  }

  override fun eval(`val`: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

  override fun new(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): ArrayNeqExpr<IndexType, ElemType> = of(leftOp, rightOp)

  override fun toString(): String = super.toString()

  object Serializer : KSerializer<ArrayNeqExpr<out Type, out Type>> {
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("ArrayNeq") {
      element<Expr<out Type>>("leftOp")
      element<Expr<out Type>>("rightOp")
    }
    override fun serialize(encoder: Encoder, value: ArrayNeqExpr<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.leftOp)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.rightOp)
      }
    override fun deserialize(decoder: Decoder): ArrayNeqExpr<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var leftOp: Expr<ArrayType<Type, Type>>? = null
        var rightOp: Expr<ArrayType<Type, Type>>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> leftOp = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class)) as Expr<ArrayType<Type, Type>>
            1 -> rightOp = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class)) as Expr<ArrayType<Type, Type>>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        ArrayNeqExpr(
          leftOp ?: throw SerializationException("Missing leftOp"),
          rightOp ?: throw SerializationException("Missing rightOp")
        )
      }
  }
}
