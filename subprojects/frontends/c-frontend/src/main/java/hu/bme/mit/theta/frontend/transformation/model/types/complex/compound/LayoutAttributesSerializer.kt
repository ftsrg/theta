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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound

import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/** [ObjectLayout.Attributes] is a Java record, which the serialization plugin cannot see. */
object LayoutAttributesSerializer : KSerializer<ObjectLayout.Attributes> {
  @Serializable
  @SerialName("theta.LayoutAttributes")
  private class Form(val packed: Boolean, val alignedToBits: Int)

  override val descriptor = Form.serializer().descriptor

  override fun serialize(encoder: Encoder, value: ObjectLayout.Attributes) =
    encoder.encodeSerializableValue(Form.serializer(), Form(value.packed, value.alignedToBits))

  override fun deserialize(decoder: Decoder): ObjectLayout.Attributes =
    decoder.decodeSerializableValue(Form.serializer()).let {
      ObjectLayout.Attributes(it.packed, it.alignedToBits)
    }
}
