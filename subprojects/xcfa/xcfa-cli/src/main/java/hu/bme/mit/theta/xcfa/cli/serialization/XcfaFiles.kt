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
package hu.bme.mit.theta.xcfa.cli.serialization

import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSerialization
import java.io.File
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.protobuf.ProtoBuf

/**
 * How xcfa-cli writes a built XCFA: ProtoBuf for a worker process, which then skips parsing, and
 * JSON for a person to read.
 */
@OptIn(ExperimentalSerializationApi::class)
object XcfaFiles {

  val module =
    XcfaSerialization.module(
      SerializersModule {
        polymorphic(MetaData::class) { subclass(CMetaData::class, CMetaData.serializer()) }
      }
    )

  val protoBuf = ProtoBuf { serializersModule = module }

  // The default discriminator "type" clashes with properties of that name.
  val json = Json {
    serializersModule = module
    classDiscriminator = "#class"
  }

  /** The name of the resource next to this class holding the format hash of [module]. */
  const val FORMAT_HASH_RESOURCE = "xcfa-format-hash"

  /** [XcfaSerialization.computeFormatHash] of [module], as the build computed it. */
  val formatHash: String by lazy {
    val stream =
      checkNotNull(XcfaFiles::class.java.getResourceAsStream(FORMAT_HASH_RESOURCE)) {
        "No $FORMAT_HASH_RESOURCE resource: the build's xcfaFormatHash task writes it"
      }
    stream.use { it.readBytes().decodeToString().trim() }
  }

  fun encode(xcfa: XCFA, parseContext: ParseContext): ByteArray =
    XcfaSerialization.encodeToByteArray(protoBuf, formatHash, xcfa, parseContext)

  fun decode(bytes: ByteArray): Pair<XCFA, ParseContext> =
    XcfaSerialization.decodeFromByteArray(protoBuf, formatHash, bytes)

  fun write(file: File, xcfa: XCFA, parseContext: ParseContext) =
    file.writeBytes(encode(xcfa, parseContext))

  fun read(file: File): Pair<XCFA, ParseContext> = decode(file.readBytes())

  fun writeJson(file: File, xcfa: XCFA, parseContext: ParseContext) =
    file.writeText(XcfaSerialization.encodeToString(json, formatHash, xcfa, parseContext))
}
