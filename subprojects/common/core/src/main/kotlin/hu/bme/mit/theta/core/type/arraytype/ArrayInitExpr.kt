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
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.PairSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * ArrayInitExpr is a way to specify arbitrary array 'literals' that may contain non-literal
 * elements as well. Note that while this class is a descendant of MultiaryExpr, it is used in a
 * non-standard way: - ops is only used as a generic Type type, - ops are solely used for
 * inter-object interactions, intra-class the `elems` and `elseElem` are used. - `elems` and
 * `elseElem` are mapped to `ops` by first placing the `elseElem`, then all indices, then all
 * elements.
 */
@Serializable(with = ArrayInitExpr.Serializer::class)
@SerialName("ArrayInit")
data class ArrayInitExpr<IndexType : Type, ElemType : Type>(
  val elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
  val elseElem: Expr<ElemType>,
  override val type: ArrayType<IndexType, ElemType>,
) : MultiaryExpr<Type, ArrayType<IndexType, ElemType>>() {

  @Suppress("UNCHECKED_CAST")
  override val ops: List<Expr<Type>> =
    listOf(elseElem as Expr<Type>) +
      elements.map { it.first as Expr<Type> } +
      elements.map { it.second as Expr<Type> }

  companion object {

    private const val OPERATOR_LABEL = "arrayinit"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      elems: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
      elseElem: Expr<ElemType>,
      type: ArrayType<IndexType, ElemType>,
    ) = ArrayInitExpr(elems, elseElem, type)

    @JvmStatic
    @Suppress("UNCHECKED_CAST")
    fun <IndexType : Type, ElemType : Type> create(
      elems: List<Pair<Expr<out Type>, Expr<out Type>>>,
      elseElem: Expr<*>,
      type: ArrayType<*, *>,
    ): ArrayInitExpr<IndexType, ElemType> =
      of(
        elems.map { Pair(it.first as Expr<IndexType>, it.second as Expr<ElemType>) },
        elseElem as Expr<ElemType>,
        type as ArrayType<IndexType, ElemType>,
      )
  }

  override fun eval(`val`: Valuation): LitExpr<ArrayType<IndexType, ElemType>> =
    ArrayLitExpr.of(
      elements.map { Pair(it.first.eval(`val`), it.second.eval(`val`)) },
      elseElem,
      type,
    )

  @Suppress("UNCHECKED_CAST")
  override fun with(ops: Iterable<Expr<Type>>): MultiaryExpr<Type, ArrayType<IndexType, ElemType>> {
    val size = ops.count()
    require(size % 2 == 1) { "Ops must be odd long!" }
    val elseElem: Expr<ElemType> = ops.first() as Expr<ElemType>
    val indices = mutableListOf<Expr<IndexType>>()
    val elems = mutableListOf<Expr<ElemType>>()
    ops.forEachIndexed { counter, op ->
      when {
        counter == 0 -> {}
        counter <= (size - 1) / 2 -> indices.add(op as Expr<IndexType>)
        else -> elems.add(op as Expr<ElemType>)
      }
    }
    val newOps = indices.indices.map { i -> indices[i] to elems[i] }
    return of(newOps, elseElem, type)
  }

  override fun new(ops: List<Expr<Type>>): MultiaryExpr<Type, ArrayType<IndexType, ElemType>> =
    with(ops)

  @Suppress("UNCHECKED_CAST")
  override fun withOps(ops: List<Expr<*>>): MultiaryExpr<Type, ArrayType<IndexType, ElemType>> =
    with(ops.map { it as Expr<Type> })

  override val operatorLabel: String = OPERATOR_LABEL

  override fun toString(): String = "arrayinit($elements, $elseElem, $type)"

  object Serializer : KSerializer<ArrayInitExpr<out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("ArrayInit") {
        element<List<Pair<Expr<out Type>, Expr<out Type>>>>("elements")
        element<Expr<out Type>>("elseElem")
        element<ArrayType<out Type, out Type>>("type")
      }

    override fun serialize(encoder: Encoder, value: ArrayInitExpr<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(
          descriptor,
          0,
          ListSerializer(
            PairSerializer(PolymorphicSerializer(Expr::class), PolymorphicSerializer(Expr::class))
          ),
          value.elements,
        )
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.elseElem)
        encodeSerializableElement(descriptor, 2, PolymorphicSerializer(Type::class), value.type)
      }

    override fun deserialize(decoder: Decoder): ArrayInitExpr<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var elements: List<Pair<Expr<Type>, Expr<Type>>>? = null
        var elseElem: Expr<Type>? = null
        var type: ArrayType<Type, Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 ->
              elements =
                decodeSerializableElement(
                  descriptor,
                  0,
                  ListSerializer(
                    PairSerializer(
                      PolymorphicSerializer(Expr::class),
                      PolymorphicSerializer(Expr::class),
                    )
                  ),
                )
                  as List<Pair<Expr<Type>, Expr<Type>>>
            1 ->
              elseElem =
                decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class))
                  as Expr<Type>
            2 ->
              type =
                decodeSerializableElement(descriptor, 2, PolymorphicSerializer(Type::class))
                  as ArrayType<Type, Type>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        ArrayInitExpr(
          elements ?: throw SerializationException("Missing elements"),
          elseElem ?: throw SerializationException("Missing elseElem"),
          type ?: throw SerializationException("Missing type"),
        )
      }
  }
}
