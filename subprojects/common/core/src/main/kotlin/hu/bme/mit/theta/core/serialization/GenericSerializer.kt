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

package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import kotlinx.serialization.KSerializer
import kotlinx.serialization.PolymorphicSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

class ArrayTypeSerializer : KSerializer<ArrayType<out Type, out Type>> {

    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("ArrayType") {
        element<String>("indexType")
        element<String>("elemType")
    }

    override fun serialize(encoder: Encoder, value: ArrayType<out Type, out Type>) =
        encoder.encodeStructure(descriptor) {
            encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class), value.indexType)
            encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.elemType)
        }

    override fun deserialize(decoder: Decoder): ArrayType<Type, Type> = decoder.decodeStructure(descriptor) {
        var indexType: Type? = null
        var elemType: Type? = null

        while (true) {
            when (val index = decodeElementIndex(descriptor)) {
                0 -> indexType = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))
                1 -> elemType = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
                CompositeDecoder.DECODE_DONE -> break
                else -> error("Unexpected index: $index")
            }
        }

        ArrayType(
            indexType = indexType ?: error("Missing indexType"),
            elemType = elemType ?: error("Missing elemType")
        )
    }
}