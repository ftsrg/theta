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

/** Write expression for array types. */
@Serializable(with = ArrayWriteExpr.Serializer::class)
@SerialName("ArrayWrite")
data class ArrayWriteExpr<IndexType : Type, ElemType : Type>(
  val array: Expr<ArrayType<IndexType, ElemType>>,
  val index: Expr<IndexType>,
  val elem: Expr<ElemType>,
) : Expr<ArrayType<IndexType, ElemType>> {

  companion object {

    private const val OPERATOR_LABEL = "write"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      array: Expr<ArrayType<IndexType, ElemType>>,
      index: Expr<IndexType>,
      elem: Expr<ElemType>,
    ) = ArrayWriteExpr(array, index, elem)

    @JvmStatic
    @Suppress("UNCHECKED_CAST")
    fun <IndexType : Type, ElemType : Type> create(
      array: Expr<*>,
      index: Expr<*>,
      elem: Expr<*>,
    ): ArrayWriteExpr<IndexType, ElemType> {
      val arrayType = array.type as ArrayType<IndexType, ElemType>
      val newArray = cast(array, arrayType)
      val newIndex = cast(index, arrayType.indexType)
      val newElem = cast(elem, arrayType.elemType)
      return of(newArray, newIndex, newElem)
    }
  }

  override val ops: List<Expr<*>> = listOf(array, index, elem)

  override val type: ArrayType<IndexType, ElemType> = ArrayType(index.type, elem.type)

  override fun eval(`val`: Valuation): LitExpr<ArrayType<IndexType, ElemType>> {
    val arrayVal = array.eval(`val`) as ArrayLitExpr<IndexType, ElemType>
    val indexVal = index.eval(`val`)
    val elemVal = elem.eval(`val`)
    val elemList = arrayVal.elements.filter { it.first != indexVal } + Pair(indexVal, elemVal)
    return ArrayLitExpr.of(elemList, arrayVal.elseElem, arrayVal.type)
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(index).add(elem).toString()

  override fun withOps(ops: List<Expr<*>>): ArrayWriteExpr<IndexType, ElemType> {
    require(ops.size == 3)
    val newArray = cast(ops[0], array.type)
    val newIndex = cast(ops[1], index.type)
    val newElem = cast(ops[2], elem.type)
    return with(newArray, newIndex, newElem)
  }

  fun with(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
    elem: Expr<ElemType>,
  ): ArrayWriteExpr<IndexType, ElemType> =
    if (this.array === array && this.index === index && this.elem === elem) {
      this
    } else {
      of(array, index, elem)
    }

  fun withIndex(index: Expr<IndexType>): ArrayWriteExpr<IndexType, ElemType> =
    with(array, index, elem)

  fun withElem(elem: Expr<ElemType>): ArrayWriteExpr<IndexType, ElemType> = with(array, index, elem)

  object Serializer : KSerializer<ArrayWriteExpr<out Type, out Type>> {
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("ArrayWrite") {
      element<Expr<out Type>>("array")
      element<Expr<out Type>>("index")
      element<Expr<out Type>>("elem")
    }
    override fun serialize(encoder: Encoder, value: ArrayWriteExpr<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.array)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.index)
        encodeSerializableElement(descriptor, 2, PolymorphicSerializer(Expr::class), value.elem)
      }
    override fun deserialize(decoder: Decoder): ArrayWriteExpr<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var array: Expr<ArrayType<Type, Type>>? = null
        var index: Expr<Type>? = null
        var elem: Expr<Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> array = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class)) as Expr<ArrayType<Type, Type>>
            1 -> index = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class)) as Expr<Type>
            2 -> elem = decodeSerializableElement(descriptor, 2, PolymorphicSerializer(Expr::class)) as Expr<Type>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        ArrayWriteExpr(
          array ?: throw SerializationException("Missing array"),
          index ?: throw SerializationException("Missing index"),
          elem ?: throw SerializationException("Missing elem")
        )
      }
  }
}
