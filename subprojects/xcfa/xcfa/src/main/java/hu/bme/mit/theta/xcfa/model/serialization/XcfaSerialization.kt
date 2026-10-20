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

import hu.bme.mit.theta.core.serialization.CoreTableClasses
import hu.bme.mit.theta.core.serialization.ObjectTable
import hu.bme.mit.theta.core.serialization.TableClass
import hu.bme.mit.theta.core.serialization.TableClasses
import hu.bme.mit.theta.core.serialization.TypeReferenceSerializer
import hu.bme.mit.theta.core.serialization.formatFingerprint
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.TraceabilityInfo
import hu.bme.mit.theta.frontend.FrontendTableClasses
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.LaidOutValue
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSerializationSession.Companion.use
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.utils.MallocLitExpr
import java.math.BigInteger
import kotlin.reflect.KClass
import kotlinx.serialization.BinaryFormat
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.PolymorphicSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerializationException
import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.StringFormat
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.SerializersModuleCollector
import kotlinx.serialization.modules.plus
import kotlinx.serialization.modules.polymorphic

/** Builder metadata is free-form; only marker and scalar values can be carried over. */
@Serializable
sealed class BuilderValue {
  @Serializable @SerialName("marker") data object Marker : BuilderValue()

  @Serializable @SerialName("int") data class IntValue(val value: Int) : BuilderValue()

  @Serializable @SerialName("bool") data class Bool(val value: Boolean) : BuilderValue()

  @Serializable @SerialName("string") data class Str(val value: String) : BuilderValue()

  @Serializable @SerialName("bigint") data class BigInt(val value: String) : BuilderValue()

  fun toValue(): Any =
    when (this) {
      Marker -> Unit
      is IntValue -> value
      is Bool -> value
      is Str -> value
      is BigInt -> BigInteger(value)
    }

  companion object {
    /** Caches ReferenceElimination keeps for itself while the passes run. */
    val PASS_INTERNAL_KEYS = setOf("references", "complexSplitGlobals")

    fun of(map: Map<String, Any>): Map<String, BuilderValue> =
      map.entries
        .filter { it.key !in PASS_INTERNAL_KEYS }
        .associate { (k, v) ->
          k to
            when (v) {
              Unit -> Marker
              is Int -> IntValue(v)
              is Boolean -> Bool(v)
              is String -> Str(v)
              is BigInteger -> BigInt(v.toString())
              else ->
                error("Builder metadata '$k' has a value of unsupported type ${v.javaClass.name}")
            }
        }
  }
}

@Serializable
class ProcedureSurrogate(
  val procedure: XcfaProcedure,
  val unsafeUnrollUsed: Boolean,
  val builderMetaData: Map<String, BuilderValue>,
)

@Serializable class InitProcedureSurrogate(val procedure: Int, val params: List<Expr<*>>)

/**
 * The XCFA itself is not a data class (it is built from procedure builders), so it goes through
 * this surrogate; everything below it is serialized by the generated serializers of the model.
 */
@Serializable
class XcfaSurrogate(
  val name: String,
  val unsafeUnrollUsed: Boolean,
  val locationCounter: Int,
  val globalVars: List<XcfaGlobalVar>,
  val procedures: List<ProcedureSurrogate>,
  val initProcedures: List<InitProcedureSurrogate>,
  val builderMetaData: Map<String, BuilderValue>,
) {

  /** Rebuilt through builders without passes, so that builder-based code keeps working. */
  fun toXcfa(): XCFA {
    XcfaLocation.cnt = maxOf(XcfaLocation.cnt, locationCounter)
    val xcfaBuilder = XcfaBuilder(name, LinkedHashSet(globalVars))
    builderMetaData.forEach { (k, v) -> xcfaBuilder.metaData[k] = v.toValue() }
    val builders =
      procedures.map { surrogate ->
        val p = surrogate.procedure
        p.edges.forEach {
          it.source.outgoingEdges.add(it)
          it.target.incomingEdges.add(it)
        }
        XcfaProcedureBuilder(
            p.name,
            ProcedurePassManager(),
            p.params.toMutableList(),
            LinkedHashSet(p.vars),
            LinkedHashSet(p.locs),
            LinkedHashSet(p.edges),
            unsafeUnrollUsed = surrogate.unsafeUnrollUsed,
            prop = p.prop,
          )
          .also { builder ->
            surrogate.builderMetaData.forEach { (k, v) -> builder.metaData[k] = v.toValue() }
            builder.copyMetaLocs(p.initLoc, p.finalLoc, p.errorLoc)
            xcfaBuilder.addProcedure(builder)
          }
      }
    initProcedures.forEach { xcfaBuilder.addEntryPoint(builders[it.procedure], it.params) }
    return xcfaBuilder.build().also { it.unsafeUnrollUsed = unsafeUnrollUsed }
  }

  companion object {

    /** XCFA fields that are recomputed (caches) or rebuilt (builders) rather than stored. */
    val DERIVED_FIELDS =
      setOf(
        "procedureBuilders",
        "initProcedureBuilders",
        "cachedHash",
        "pointsToGraph\$delegate",
        "pointerPartitions",
      )
    val COVERED_FIELDS =
      setOf("name", "globalVars", "procedures", "initProcedures", "unsafeUnrollUsed")

    fun of(xcfa: XCFA): XcfaSurrogate {
      val builders = xcfa.procedureBuilders.associateBy { it.name }
      val procedures = xcfa.procedures.toList()
      val index = procedures.withIndex().associate { (i, p) -> p to i }
      return XcfaSurrogate(
        name = xcfa.name,
        unsafeUnrollUsed = xcfa.unsafeUnrollUsed,
        locationCounter = XcfaLocation.cnt,
        globalVars = xcfa.globalVars.toList(),
        procedures =
          procedures.map {
            val builder = builders[it.name]
            ProcedureSurrogate(
              it,
              builder?.unsafeUnrollUsed ?: false,
              BuilderValue.of(builder?.metaData ?: emptyMap()),
            )
          },
        initProcedures =
          xcfa.initProcedures.map { InitProcedureSurrogate(index[it.first]!!, it.second) },
        builderMetaData =
          BuilderValue.of(xcfa.procedureBuilders.firstOrNull()?.parent?.metaData ?: emptyMap()),
      )
    }
  }
}

/** The metadata, after the objects it may refer to. */
private object MetaDataTable : KSerializer<List<MetaData>> {
  private val delegate = ListSerializer(PolymorphicSerializer(MetaData::class))
  override val descriptor = delegate.descriptor

  override fun serialize(encoder: Encoder, value: List<MetaData>) =
    encoder.encodeSerializableValue(delegate, value)

  override fun deserialize(decoder: Decoder): List<MetaData> =
    decoder.decodeSerializableValue(delegate).also {
      XcfaSerializationSession.get().metas.addAll(it)
    }
}

/** The parse context, which the C types in the object table share. */
private object ParseContextEntry : KSerializer<ParseContext> {
  override val descriptor = ParseContext.serializer().descriptor

  override fun serialize(encoder: Encoder, value: ParseContext) =
    encoder.encodeSerializableValue(ParseContext.serializer(), value)

  override fun deserialize(decoder: Decoder): ParseContext =
    decoder.decodeSerializableValue(ParseContext.serializer()).also {
      XcfaSerializationSession.get().decoded(it)
    }
}

/** The writer's format: a reader of another one stops here instead of misreading the rest. */
private object FormatHeader : KSerializer<String> {
  override val descriptor = PrimitiveSerialDescriptor("theta.XcfaFormat", PrimitiveKind.STRING)

  override fun serialize(encoder: Encoder, value: String) = encoder.encodeString(value)

  override fun deserialize(decoder: Decoder): String {
    val format = decoder.decodeString()
    val expected = XcfaSerializationSession.get().formatHash
    if (format != expected) {
      throw SerializationException(
        "The XCFA was written in serialization format $format, this build reads $expected"
      )
    }
    return format
  }
}

/** The tables come first: decoding resolves every reference as soon as it reads it. */
@Serializable
class XcfaPayload(
  @Serializable(with = FormatHeader::class) val format: String,
  @Serializable(with = ParseContextEntry::class) val parseContext: ParseContext,
  @Serializable(with = ObjectTable.Serializer::class) val objects: ObjectTable,
  @Serializable(with = MetaDataTable::class) val metas: List<MetaData>,
  val frontendMetadata: FrontendMetadataSurrogate,
  val xcfa: XcfaSurrogate,
)

object XcfaSerialization {

  /**
   * The module a format must be configured with. [metaData] registers the [MetaData] subclasses of
   * the frontend in use (e.g. CMetaData); polymorphic serialization fails on unregistered ones.
   */
  @Suppress("UNCHECKED_CAST")
  fun module(metaData: SerializersModule): SerializersModule =
    SerializersModule {
      contextual(MetaData::class, MetaDataReferenceSerializer)
      polymorphic(MetaData::class) { subclass(EmptyMetaData::class, EmptyMetaData.serializer()) }
      polymorphic(TraceabilityInfo::class) {
        subclass(LaidOutValue::class, LaidOutValue.serializer())
        defaultDeserializer { if (it == CTypeInfoSerializer.NAME) CTypeInfoSerializer else null }
      }
      polymorphicDefaultSerializer(TraceabilityInfo::class) {
        if (it is CComplexType) CTypeInfoSerializer as SerializationStrategy<TraceabilityInfo>
        else null
      }
    } + metaData

  private object XcfaTableClasses : TableClasses() {
    override val names: Set<String> = setOf("hu.bme.mit.theta.xcfa.utils.MallocLitExpr")

    override fun entry(name: String): TableClass =
      when (name) {
        "hu.bme.mit.theta.xcfa.utils.MallocLitExpr" ->
          TableClass(MallocLitExpr::class.java, MallocLitExpr.serializer(TypeReferenceSerializer))
        else -> error("No entry for $name")
      }
  }

  /** Every class whose objects the object table may hold. */
  val tableClasses: TableClasses = CoreTableClasses + FrontendTableClasses + XcfaTableClasses

  /**
   * A hash of the shapes of everything an XCFA is written with in [module] (see
   * [formatFingerprint]): two builds read each other's output exactly when they agree on it. It
   * loads every serialized class, so it is computed when building (xcfa-cli's `xcfaFormatHash`
   * task), and encoding and decoding are given the result.
   */
  @OptIn(ExperimentalSerializationApi::class)
  fun computeFormatHash(module: SerializersModule): String {
    val descriptors = ArrayList<SerialDescriptor>()
    tableClasses.all.forEach { descriptors.add(it.serializer.descriptor) }
    descriptors.add(XcfaPayload.serializer().descriptor)
    descriptors.add(CTypeInfoSerializer.descriptor)
    module.dumpTo(
      object : SerializersModuleCollector {
        override fun <T : Any> contextual(
          kClass: KClass<T>,
          provider: (typeArgumentsSerializers: List<KSerializer<*>>) -> KSerializer<*>,
        ) {}

        override fun <Base : Any, Sub : Base> polymorphic(
          baseClass: KClass<Base>,
          actualClass: KClass<Sub>,
          actualSerializer: KSerializer<Sub>,
        ) {
          descriptors.add(actualSerializer.descriptor)
        }

        override fun <Base : Any> polymorphicDefaultSerializer(
          baseClass: KClass<Base>,
          defaultSerializerProvider: (value: Base) -> SerializationStrategy<Base>?,
        ) {}

        override fun <Base : Any> polymorphicDefaultDeserializer(
          baseClass: KClass<Base>,
          defaultDeserializerProvider: (className: String?) -> DeserializationStrategy<Base>?,
        ) {}
      }
    )
    return formatFingerprint(descriptors)
  }

  private fun payload(s: XcfaSerializationSession, xcfa: XCFA): XcfaPayload {
    val surrogate = XcfaSurrogate.of(xcfa)
    s.objects.collect(XcfaSurrogate.serializer(), surrogate)
    val frontendMetadata = FrontendMetadataSurrogate.of(s)
    s.objects.collect(ListSerializer(PolymorphicSerializer(MetaData::class)), s.metaList)
    s.objects.complete()
    s.collecting = false
    return XcfaPayload(
      s.formatHash,
      s.parseContext,
      s.objects,
      s.metaList,
      frontendMetadata,
      surrogate,
    )
  }

  // Each function takes the format's hash (see computeFormatHash): it is written first, and a file
  // starting with another one is refused.

  fun encodeToByteArray(
    format: BinaryFormat,
    formatHash: String,
    xcfa: XCFA,
    parseContext: ParseContext,
  ): ByteArray {
    val s = XcfaSerializationSession(parseContext, format.serializersModule, formatHash)
    return s.use { format.encodeToByteArray(XcfaPayload.serializer(), payload(s, xcfa)) }
  }

  fun encodeToString(
    format: StringFormat,
    formatHash: String,
    xcfa: XCFA,
    parseContext: ParseContext,
  ): String {
    val s = XcfaSerializationSession(parseContext, format.serializersModule, formatHash)
    return s.use { format.encodeToString(XcfaPayload.serializer(), payload(s, xcfa)) }
  }

  private fun finish(s: XcfaSerializationSession, payload: XcfaPayload): Pair<XCFA, ParseContext> {
    payload.frontendMetadata.applyTo(s)
    return payload.xcfa.toXcfa() to s.parseContext
  }

  fun decodeFromByteArray(
    format: BinaryFormat,
    formatHash: String,
    bytes: ByteArray,
  ): Pair<XCFA, ParseContext> {
    val s = XcfaSerializationSession(null, format.serializersModule, formatHash)
    return s.use { finish(s, format.decodeFromByteArray(XcfaPayload.serializer(), bytes)) }
  }

  fun decodeFromString(
    format: StringFormat,
    formatHash: String,
    string: String,
  ): Pair<XCFA, ParseContext> {
    val s = XcfaSerializationSession(null, format.serializersModule, formatHash)
    return s.use { finish(s, format.decodeFromString(XcfaPayload.serializer(), string)) }
  }
}
