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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Represents a reference to a declaration.
 *
 * @param DeclType The type of the declaration
 */
@Serializable(with = RefExpr.Serializer::class)
@SerialName("Ref")
data class RefExpr<DeclType : Type>(val decl: Decl<DeclType>) : NullaryExpr<DeclType>() {

  companion object {

    @JvmStatic fun <T : Type> of(decl: Decl<T>): RefExpr<T> = RefExpr(decl)
  }

  override val type: DeclType = decl.type

  override fun eval(`val`: Valuation): LitExpr<DeclType> =
    `val`.eval(decl).orElseThrow {
      IllegalStateException("No value found for declaration: ${decl.name}")
    }

  override fun toString(): String = decl.name

  object Serializer : KSerializer<RefExpr<out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("Ref") { element<Decl<out Type>>("decl") }

    override fun serialize(encoder: Encoder, value: RefExpr<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Decl::class), value.decl)
      }

    override fun deserialize(decoder: Decoder): RefExpr<out Type> =
      decoder.decodeStructure(descriptor) {
        var decl: Decl<out Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> decl = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Decl::class))
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        RefExpr(decl = decl ?: throw SerializationException("Missing decl "))
      }
  }
}
