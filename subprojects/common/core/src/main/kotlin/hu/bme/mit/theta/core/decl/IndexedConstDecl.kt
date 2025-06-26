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
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * A constant declaration that belongs to a variable ([VarDecl] declaration for a given index. For
 * example, when unfolding a path, each variable will have a new constant for each step of the path.
 *
 * @param <DeclType>
 */
@Serializable(with = IndexedConstDecl.Serializer::class)
@SerialName("IndexedConstDecl")
data class IndexedConstDecl<DeclType : Type>(val varDecl: VarDecl<DeclType>, val index: Int) :
  ConstDecl<DeclType>() {

  init {
    require(index >= 0) { "Index must be non-negative" }
  }

  companion object {

    private const val NAME_FORMAT: String = "_%s:%d"
  }

  override val name: String = String.format(NAME_FORMAT, varDecl.name, index)
  override val type: DeclType = varDecl.type

  object Serializer : KSerializer<IndexedConstDecl<out Type>> {

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("IndexedConstDecl") {
        element<VarDecl<out Type>>("varDecl")
        element<Int>("index")
      }

    override fun serialize(encoder: Encoder, value: IndexedConstDecl<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, VarDecl.Serializer, value.varDecl)
        encodeIntElement(descriptor, 1, value.index)
      }

    override fun deserialize(decoder: Decoder): IndexedConstDecl<out Type> =
      decoder.decodeStructure(descriptor) {
        var varDecl: VarDecl<out Type>? = null
        var index: Int? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> varDecl = decodeSerializableElement(descriptor, 0, VarDecl.Serializer)
            1 -> index = decodeIntElement(descriptor, 1)
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        IndexedConstDecl(
          varDecl = varDecl ?: error("Missing varDecl"),
          index = index ?: error("Missing index"),
        )
      }
  }
}
