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
package hu.bme.mit.theta.xcfa.model.serialization

import hu.bme.mit.theta.core.serialization.ObjectTable
import hu.bme.mit.theta.core.serialization.ObjectTable.Companion.use
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.IdentityHashMap
import java.util.Optional
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.modules.SerializersModule

/**
 * The state of one encode (of the [encoded] parse context's XCFA) or decode (when it is null).
 * Types, declarations, expressions, statements and C types live in the [objects] table (see
 * [ObjectTable]); metadata and locations have tables of their own, as edges point at location
 * objects. [formatHash] is the one written, or the one a decoded file must start with.
 */
class XcfaSerializationSession
internal constructor(
  encoded: ParseContext?,
  module: SerializersModule,
  internal val formatHash: String,
) {

  private val decoding = encoded == null

  /**
   * The C types' parse context: given when encoding, read before the object table when decoding.
   */
  internal lateinit var parseContext: ParseContext
    private set

  internal val objects: ObjectTable =
    if (decoding) ObjectTable.forDecoding(module, XcfaSerialization.tableClasses)
    else
      ObjectTable.forEncoding(
        module,
        XcfaSerialization.tableClasses,
        internKey = ::internKey,
        ambient = listOfNotNull(encoded),
      )

  init {
    encoded?.let { parseContext = it }
  }

  internal fun decoded(parseContext: ParseContext) {
    this.parseContext = parseContext
    objects.addAmbient(parseContext)
  }

  /** While true (first encoding pass), unseen metadata is added; afterwards it is an error. */
  internal var collecting = !decoding

  private val metaIds = IdentityHashMap<MetaData, Int>()
  private val locIds = IdentityHashMap<XcfaLocation, Int>()

  internal val metaList = ArrayList<MetaData>()
  internal val metas = ArrayList<MetaData>()
  internal val locs = ArrayList<XcfaLocation>()

  // C types are hash-consed: the parser re-expands struct types on every use, so the same type
  // exists as thousands of objects. Nothing keys on their identity, and their equals ignores
  // some state (e.g. a pointer's isFunctionPointer), so they are compared by what is written.
  private fun internKey(value: Any): Any? =
    when (value) {
      is Type -> value
      is CComplexType -> objects.definitionKey(value)
      else -> null
    }

  internal fun ctypeId(t: CComplexType): Int = objects.idOf(t)

  internal fun ctype(i: Int): CComplexType = objects.valueAt(i) as CComplexType

  internal fun exprId(e: Expr<*>): Int = objects.idOf(e)

  internal fun expr(i: Int): Expr<*> = objects.valueAt(i) as Expr<*>

  internal fun metaId(m: MetaData): Int =
    if (m === EmptyMetaData) -1
    else
      metaIds[m]
        ?: run {
          check(collecting) { "Not collected in the first pass: ${m.javaClass.name} $m" }
          metaList.add(m)
          (metaList.size - 1).also { metaIds[m] = it }
        }

  internal fun locId(l: XcfaLocation, define: Boolean): Int =
    locIds[l]
      ?: run {
        check(define && collecting) { "Location ${l.name} referenced before its definition" }
        locIds.size.also { locIds[l] = it }
      }

  companion object {

    private val current = ThreadLocal<XcfaSerializationSession>()

    internal fun get(): XcfaSerializationSession =
      current.get() ?: error("XCFA serializers can only be used through XcfaSerialization")

    internal fun <T> XcfaSerializationSession.use(block: () -> T): T {
      check(current.get() == null) { "Nested XCFA serialization sessions are not supported" }
      current.set(this)
      try {
        return objects.use(block)
      } finally {
        current.remove()
      }
    }
  }
}

private fun session() = XcfaSerializationSession.get()

private fun intDescriptor(name: String) = PrimitiveSerialDescriptor(name, PrimitiveKind.INT)

object MetaDataReferenceSerializer : KSerializer<MetaData> {
  override val descriptor = intDescriptor("theta.MetaDataRef")

  override fun serialize(encoder: Encoder, value: MetaData) =
    encoder.encodeInt(session().metaId(value))

  override fun deserialize(decoder: Decoder): MetaData =
    decoder.decodeInt().let { if (it == -1) EmptyMetaData else session().metas[it] }
}

/** Writes a location in full and gives it the index that [LocationReferenceSerializer] uses. */
object LocationDefinitionSerializer : KSerializer<XcfaLocation> {
  @OptIn(ExperimentalSerializationApi::class)
  override val descriptor =
    SerialDescriptor("theta.LocationDefinition", XcfaLocation.serializer().descriptor)

  override fun serialize(encoder: Encoder, value: XcfaLocation) {
    session().locId(value, define = true)
    encoder.encodeSerializableValue(XcfaLocation.serializer(), value)
  }

  override fun deserialize(decoder: Decoder): XcfaLocation =
    decoder.decodeSerializableValue(XcfaLocation.serializer()).also { session().locs.add(it) }
}

object LocationReferenceSerializer : KSerializer<XcfaLocation> {
  override val descriptor = intDescriptor("theta.LocationRef")

  override fun serialize(encoder: Encoder, value: XcfaLocation) =
    encoder.encodeInt(session().locId(value, define = false))

  override fun deserialize(decoder: Decoder): XcfaLocation = session().locs[decoder.decodeInt()]
}

object OptionalLocationReferenceSerializer : KSerializer<Optional<XcfaLocation>> {
  override val descriptor = intDescriptor("theta.OptionalLocationRef")

  override fun serialize(encoder: Encoder, value: Optional<XcfaLocation>) =
    encoder.encodeInt(value.map { session().locId(it, define = false) }.orElse(-1))

  override fun deserialize(decoder: Decoder): Optional<XcfaLocation> =
    decoder.decodeInt().let { if (it == -1) Optional.empty() else Optional.of(session().locs[it]) }
}

/**
 * A C type where a [hu.bme.mit.theta.core.type.TraceabilityInfo] is expected: polymorphic
 * serialization needs a class-like value, so the reference is wrapped in one.
 */
object CTypeInfoSerializer : KSerializer<CComplexType> {
  const val NAME = "ctype"

  override val descriptor: SerialDescriptor =
    buildClassSerialDescriptor(NAME) { element("id", intDescriptor("theta.CTypeRef")) }

  override fun serialize(encoder: Encoder, value: CComplexType) {
    val composite = encoder.beginStructure(descriptor)
    composite.encodeIntElement(descriptor, 0, session().ctypeId(value))
    composite.endStructure(descriptor)
  }

  override fun deserialize(decoder: Decoder): CComplexType {
    val composite = decoder.beginStructure(descriptor)
    var id = -1
    while (true) {
      val index = composite.decodeElementIndex(descriptor)
      if (index < 0) break
      id = composite.decodeIntElement(descriptor, index)
    }
    composite.endStructure(descriptor)
    check(id >= 0) { "A C type reference needs its index" }
    return session().ctype(id)
  }
}
