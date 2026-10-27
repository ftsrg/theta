/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.Tuple2
import java.math.BigInteger
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerializationException
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.CompositeDecoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.decodeStructure
import kotlinx.serialization.encoding.encodeStructure

/** In decimal, as integers of any size are. */
object BigIntegerSerializer : KSerializer<BigInteger> {
  override val descriptor: SerialDescriptor =
    PrimitiveSerialDescriptor("theta.BigInteger", PrimitiveKind.STRING)

  override fun serialize(encoder: Encoder, value: BigInteger) =
    encoder.encodeString(value.toString())

  override fun deserialize(decoder: Decoder): BigInteger = BigInteger(decoder.decodeString())
}

/** A bit vector (index 0 is the most significant bit) as `<width>#<hex digits>`. */
object BitsSerializer : KSerializer<BooleanArray> {
  override val descriptor: SerialDescriptor =
    PrimitiveSerialDescriptor("theta.Bits", PrimitiveKind.STRING)

  override fun serialize(encoder: Encoder, value: BooleanArray) {
    val digits = (value.size + 3) / 4
    val hex = CharArray(digits)
    // The first digit holds the leftover high bits when the width is not a multiple of four.
    var bit = value.size - 1
    for (d in digits - 1 downTo 0) {
      var nibble = 0
      for (k in 0 until 4) {
        if (bit >= 0 && value[bit]) nibble = nibble or (1 shl k)
        bit--
      }
      hex[d] = Character.forDigit(nibble, 16)
    }
    encoder.encodeString("${value.size}#${String(hex)}")
  }

  override fun deserialize(decoder: Decoder): BooleanArray {
    val text = decoder.decodeString()
    val separator = text.indexOf('#')
    if (separator < 0) throw SerializationException("Malformed bit vector '$text'")
    val size = text.substring(0, separator).toInt()
    val hex = text.substring(separator + 1)
    val bits = BooleanArray(size)
    var bit = size - 1
    for (d in hex.length - 1 downTo 0) {
      val nibble = Character.digit(hex[d], 16)
      for (k in 0 until 4) {
        if (bit >= 0) bits[bit] = nibble and (1 shl k) != 0
        bit--
      }
    }
    return bits
  }
}

class Tuple2Serializer<A, B>(
  private val first: KSerializer<A>,
  private val second: KSerializer<B>,
) : KSerializer<Tuple2<A, B>> {
  override val descriptor: SerialDescriptor =
    buildClassSerialDescriptor("theta.Tuple2", first.descriptor, second.descriptor) {
      element("first", first.descriptor)
      element("second", second.descriptor)
    }

  override fun serialize(encoder: Encoder, value: Tuple2<A, B>) =
    encoder.encodeStructure(descriptor) {
      encodeSerializableElement(descriptor, 0, first, value.get1())
      encodeSerializableElement(descriptor, 1, second, value.get2())
    }

  override fun deserialize(decoder: Decoder): Tuple2<A, B> =
    decoder.decodeStructure(descriptor) {
      var a: Any? = null
      var b: Any? = null
      while (true) {
        when (val index = decodeElementIndex(descriptor)) {
          0 -> a = decodeSerializableElement(descriptor, 0, first)
          1 -> b = decodeSerializableElement(descriptor, 1, second)
          CompositeDecoder.DECODE_DONE -> break
          else -> throw SerializationException("Unexpected Tuple2 element $index")
        }
      }
      @Suppress("UNCHECKED_CAST") Tuple2.of(a as A, b as B)
    }
}
