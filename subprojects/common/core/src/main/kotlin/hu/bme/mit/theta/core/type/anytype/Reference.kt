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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Represents a reference to an expression.
 *
 * @param A The type of the reference
 * @param T The type of the expression
 * @property expr The referenced expression
 * @property type The type of the reference
 */
@Serializable(with = Reference.Serializer::class)
@SerialName("Reference")
data class Reference<A : Type, T : Type>(val expr: Expr<T>, override val type: A) : Expr<A> {

  companion object {

    @JvmStatic
    fun <A : Type, T : Type> of(expr: Expr<T>, type: A): Reference<A, T> = Reference(expr, type)
  }

  override val arity: Int = 1

  override val ops: List<Expr<*>> = listOf(expr)

  override fun eval(`val`: Valuation): LitExpr<A> =
    throw IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!")

  override fun withOps(ops: List<Expr<*>>): Expr<A> {
    require(ops.size == 1) { "Reference must have exactly one operand" }
    require(ops[0] is RefExpr<*> && (ops[0] as RefExpr<*>).decl is VarDecl<*>) {
      "Don't transform references to constants."
    }
    @Suppress("UNCHECKED_CAST") return Reference(ops[0] as Expr<T>, type)
  }

  object Serializer : KSerializer<Reference<out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("Reference") {
        element<Expr<out Type>>("expr")
        element<Type>("type")
      }

    override fun serialize(encoder: Encoder, value: Reference<out Type, out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.expr)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.type)
      }

    override fun deserialize(decoder: Decoder): Reference<out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var expr: Expr<out Type>? = null
        var type: Type? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> expr = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class))
            1 -> type = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        Reference(
          expr ?: throw SerializationException("Missing expr "),
          type ?: throw SerializationException("Missing type "),
        )
      }
  }
}
