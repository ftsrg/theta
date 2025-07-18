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
package hu.bme.mit.theta.core.decl

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.UniqueIdProvider
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * A basic constant declaration that can be directly passed to the SMT solver.
 *
 * @param <DeclType>
 */
@Serializable(with = BasicConstDecl.Serializer::class)
@SerialName("BasicConstDecl")
data class BasicConstDecl<DeclType : Type>(
  override val name: String,
  override val type: DeclType,
  override val id: Int = uniqueIdProvider.get(),
) : ConstDecl<DeclType>() {

  companion object {
    private val uniqueIdProvider = UniqueIdProvider()
  }

  object Serializer : KSerializer<BasicConstDecl<out Type>> {

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("BasicConstDecl") {
        element<String>("name")
        element<Type>("type")
        element<Int>("id")
      }

    override fun serialize(encoder: Encoder, value: BasicConstDecl<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeStringElement(descriptor, 0, value.name)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.type)
        encodeIntElement(descriptor, 2, value.id)
      }

    override fun deserialize(decoder: Decoder): BasicConstDecl<out Type> =
      decoder.decodeStructure(descriptor) {
        var name: String? = null
        var type: Type? = null
        var id: Int? = null

        while (true) {
          when (val index = decodeElementIndex(descriptor)) {
            0 -> name = decodeStringElement(descriptor, 0)
            1 -> type = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
            2 -> id = decodeIntElement(descriptor, 2)
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unexpected index: $index")
          }
        }

        BasicConstDecl(
          name = name ?: throw SerializationException("Missing name"),
          type = type ?: throw SerializationException("Missing type"),
          id = id ?: throw SerializationException("Missing id"),
        )
      }
  }
}
