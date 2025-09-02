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

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/** Represents an array type with a given index and element type. */
@Serializable(with = ArrayType.Serializer::class)
@SerialName(ArrayType.TYPE_LABEL)
data class ArrayType<IndexType : Type, ElemType : Type>(
  val indexType: IndexType,
  val elemType: ElemType,
) : Equational<ArrayType<IndexType, ElemType>> {

  companion object {

    internal const val TYPE_LABEL = "Array"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      indexType: IndexType,
      elemType: ElemType,
    ): ArrayType<IndexType, ElemType> = ArrayType(indexType, elemType)
  }

  override fun Eq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): EqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Eq(leftOp, rightOp)

  override fun Neq(
    leftOp: Expr<ArrayType<IndexType, ElemType>>,
    rightOp: Expr<ArrayType<IndexType, ElemType>>,
  ): NeqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Neq(leftOp, rightOp)

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add("([${indexType}] -> $elemType)").toString()

  override val domainSize: DomainSize
    get() = DomainSize.pow(elemType.domainSize, indexType.domainSize)

  object Serializer : KSerializer<ArrayType<out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("ArrayType") {
        element<String>("indexType")
        element<String>("elemType")
      }

    override fun serialize(encoder: Encoder, value: ArrayType<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(
          descriptor,
          0,
          PolymorphicSerializer(Type::class),
          value.indexType,
        )
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.elemType)
      }

    override fun deserialize(decoder: Decoder): ArrayType<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var indexType: Type? = null
        var elemType: Type? = null

        while (true) {
          when (val index = decodeElementIndex(descriptor)) {
            0 ->
              indexType =
                decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))
            1 ->
              elemType =
                decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unexpected index: $index")
          }
        }

        ArrayType(
          indexType = indexType ?: throw SerializationException("Missing indexType"),
          elemType = elemType ?: throw SerializationException("Missing elemType"),
        )
      }
  }
}
