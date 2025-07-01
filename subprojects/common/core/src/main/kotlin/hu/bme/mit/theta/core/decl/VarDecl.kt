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
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Represents a variable declaration. Variables cannot be directly passed to the SMT solver, they
 * must be replaced with constants for a given index ([IndexedConstDecl]). See also
 * [hu.bme.mit.theta.core.utils.PathUtils].
 *
 * @param <DeclType>
 */
@Serializable(with = VarDecl.Serializer::class)
@SerialName(VarDecl.DECL_LABEL)
data class VarDecl<DeclType : Type>(
  override val name: String,
  override val type: DeclType,
  override val id: Int = uniqueIdProvider.get(),
) : Decl<DeclType>() {

  companion object {

    private val uniqueIdProvider = UniqueIdProvider()

    internal const val DECL_LABEL: String = "var"

    fun <T : Type> copyOf(from: VarDecl<T>): VarDecl<T> = VarDecl(from.name, from.type)
  }

  @Transient private val indexToConst = mutableMapOf<Int, IndexedConstDecl<DeclType>>()

  fun getConstDecl(index: Int): IndexedConstDecl<DeclType> {
    require(index >= 0) { "Index must be non-negative" }
    return indexToConst.getOrPut(index) { IndexedConstDecl(this, index) }
  }

  override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()

  object Serializer : KSerializer<VarDecl<out Type>> {

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("VarDecl") {
        element<String>("name")
        element<Type>("type")
        element<Int>("id")
      }

    override fun serialize(encoder: Encoder, value: VarDecl<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeStringElement(descriptor, 0, value.name)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.type)
        encodeIntElement(descriptor, 2, value.id)
      }

    override fun deserialize(decoder: Decoder): VarDecl<out Type> =
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

        VarDecl(
          name = name ?: error("Missing name"),
          type = type ?: error("Missing type"),
          id = id ?: error("Missing id"),
        )
      }
  }
}
