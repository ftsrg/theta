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
package hu.bme.mit.theta.xcfa.cli.params

import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import java.io.File
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.json.Json

// Defaults are encoded too: some of them (e.g. the unroll limit) are read from mutable globals.
private val configJson = Json { encodeDefaults = true }

private val configSerializer =
  XcfaConfig.serializer(SpecFrontendConfig.serializer(), SpecBackendConfig.serializer())

@Suppress("UNCHECKED_CAST")
fun XcfaConfig<*, *>.toJson(): String =
  configJson.encodeToString(
    configSerializer,
    this as XcfaConfig<SpecFrontendConfig, SpecBackendConfig>,
  )

fun xcfaConfigFromJson(json: String): XcfaConfig<*, *> =
  configJson.decodeFromString(configSerializer, json)

object FileSerializer : KSerializer<File> {
  override val descriptor: SerialDescriptor =
    PrimitiveSerialDescriptor("java.io.File", PrimitiveKind.STRING)

  override fun serialize(encoder: Encoder, value: File) = encoder.encodeString(value.path)

  override fun deserialize(decoder: Decoder): File = File(decoder.decodeString())
}

/**
 * Leaves out the witness: it holds the parsed witness and a pass factory, and the run reading the
 * config builds both again from [InputConfig.witness] (see `determineProperty`).
 */
object XcfaPropertySerializer : KSerializer<XcfaProperty> {

  @Serializable
  @SerialName("hu.bme.mit.theta.xcfa.XcfaProperty")
  private class Surrogate(val inputProperty: ErrorDetection, val verifiedProperty: ErrorDetection)

  override val descriptor: SerialDescriptor = Surrogate.serializer().descriptor

  override fun serialize(encoder: Encoder, value: XcfaProperty) =
    encoder.encodeSerializableValue(
      Surrogate.serializer(),
      Surrogate(value.inputProperty, value.verifiedProperty),
    )

  override fun deserialize(decoder: Decoder): XcfaProperty {
    val surrogate = decoder.decodeSerializableValue(Surrogate.serializer())
    return XcfaProperty(surrogate.inputProperty).also {
      it.transformSpecification(surrogate.verifiedProperty)
    }
  }
}
