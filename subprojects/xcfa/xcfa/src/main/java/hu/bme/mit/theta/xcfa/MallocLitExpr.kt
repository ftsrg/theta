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
package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

@Serializable(with = MallocLitExpr.Serializer::class)
@SerialName("MallocLit")
data class MallocLitExpr<T : Type>(val kType: T) : NullaryExpr<T>(), LitExpr<T> {

  override val type: T
    get() = kType

  override fun eval(`val`: Valuation): LitExpr<T> = this

  object Serializer : KSerializer<MallocLitExpr<out Type>> {

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("MallocLit") { element<Type>("kType") }

    override fun serialize(encoder: Encoder, value: MallocLitExpr<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class), value.kType)
      }

    override fun deserialize(decoder: Decoder): MallocLitExpr<out Type> =
      decoder.decodeStructure(descriptor) {
        var kType: Type? = null

        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 ->
              kType = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))

            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        MallocLitExpr(kType = kType ?: throw SerializationException("Missing kType"))
      }
  }
}
