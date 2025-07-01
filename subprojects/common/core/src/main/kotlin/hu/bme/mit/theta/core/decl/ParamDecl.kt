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

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.UniqueIdProvider
import kotlinx.serialization.KSerializer
import kotlinx.serialization.PolymorphicSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

@Serializable(with = ParamDecl.Serializer::class)
@SerialName(ParamDecl.DECL_LABEL)
data class ParamDecl<DeclType : Type>(
  override val name: String,
  override val type: DeclType,
  override val id: Int = uniqueIdProvider.get(),
) : Decl<DeclType>() {

  companion object {

    private val uniqueIdProvider = UniqueIdProvider()

    internal const val DECL_LABEL: String = "Param"
  }

  override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()

  object Serializer : KSerializer<ParamDecl<out Type>> {

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("ParamDecl") {
        element<String>("name")
        element<Type>("type")
        element<Int>("id")
      }

    override fun serialize(encoder: Encoder, value: ParamDecl<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeStringElement(descriptor, 0, value.name)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.type)
        encodeIntElement(descriptor, 2, value.id)
      }

    override fun deserialize(decoder: Decoder): ParamDecl<out Type> =
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
            else -> error("Unexpected index: $index")
          }
        }

        ParamDecl(
          name = name ?: error("Missing name"),
          type = type ?: error("Missing type"),
          id = id ?: error("Missing id"),
        )
      }
  }
}
