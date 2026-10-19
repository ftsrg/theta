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
@file:UseContextualSerialization(Expr::class)

package hu.bme.mit.theta.xcfa.model.serialization

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.frontend.ParseContext
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
import java.math.BigInteger
import kotlinx.serialization.BinaryFormat
import kotlinx.serialization.KSerializer
import kotlinx.serialization.PolymorphicSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.StringFormat
import kotlinx.serialization.UseContextualSerialization
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.modules.SerializersModule
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

/** Serializes a table, and on decoding immediately rebuilds its objects into the session. */
private abstract class TableSerializer<T>(element: KSerializer<T>) : KSerializer<List<T>> {
  private val delegate = ListSerializer(element)
  override val descriptor = delegate.descriptor

  override fun serialize(encoder: Encoder, value: List<T>) =
    encoder.encodeSerializableValue(delegate, value)

  override fun deserialize(decoder: Decoder): List<T> =
    decoder.decodeSerializableValue(delegate).also {
      materialize(XcfaSerializationSession.get(), it)
    }

  abstract fun materialize(s: XcfaSerializationSession, nodes: List<T>)
}

private object ClassTable : TableSerializer<String>(String.serializer()) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<String>) {
    nodes.forEach { s.classes.add(Class.forName(it)) }
  }
}

private object DeclTable : TableSerializer<DeclNode>(DeclNode.serializer()) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<DeclNode>) {
    val types = HashMap<TypeNode, Type>()
    nodes.forEach { s.decls.add(it.toDecl(types)) }
  }
}

private object ExprTable : TableSerializer<ExprNode>(ExprNode.serializer()) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<ExprNode>) {
    val types = HashMap<TypeNode, Type>()
    s.exprs.ensureCapacity(nodes.size)
    nodes.forEach { s.exprs.add(it.toExpr(s, types)) }
  }
}

private object StmtTable : TableSerializer<StmtNode>(StmtNode.serializer()) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<StmtNode>) {
    nodes.forEach { s.stmts.add(it.toStmt(s)) }
  }
}

private object CTypeTable : TableSerializer<CTypeNode>(CTypeNode.serializer()) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<CTypeNode>) {
    nodes.forEach { s.ctypes.add(it.toCType(s)) }
  }
}

private object MetaDataTable : TableSerializer<MetaData>(PolymorphicSerializer(MetaData::class)) {
  override fun materialize(s: XcfaSerializationSession, nodes: List<MetaData>) {
    s.metas.addAll(nodes)
  }
}

/** Tables come first: decoding resolves every reference as soon as it reads it. */
@Serializable
class XcfaPayload(
  @Serializable(with = ClassTable::class) val classes: List<String>,
  @Serializable(with = DeclTable::class) val decls: List<DeclNode>,
  @Serializable(with = ExprTable::class) val exprs: List<ExprNode>,
  @Serializable(with = StmtTable::class) val stmts: List<StmtNode>,
  @Serializable(with = CTypeTable::class) val ctypes: List<CTypeNode>,
  @Serializable(with = MetaDataTable::class) val metas: List<MetaData>,
  val parseContext: ParseContextSurrogate,
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
      contextual(Expr::class, ExprReferenceSerializer as KSerializer<Expr<*>>)
      contextual(LitExpr::class, LitExprReferenceSerializer as KSerializer<LitExpr<*>>)
      contextual(VarDecl::class, VarDeclReferenceSerializer as KSerializer<VarDecl<*>>)
      contextual(Stmt::class, StmtReferenceSerializer)
      contextual(MetaData::class, MetaDataReferenceSerializer)
      polymorphic(MetaData::class) { subclass(EmptyMetaData::class, EmptyMetaData.serializer()) }
    } + metaData

  private fun payload(
    s: XcfaSerializationSession,
    xcfa: XCFA,
    module: SerializersModule,
  ): XcfaPayload {
    val surrogate = XcfaSurrogate.of(xcfa)
    val collector = CollectingEncoder(module)
    collector.encodeSerializableValue(XcfaSurrogate.serializer(), surrogate)
    val parseContext = ParseContextSurrogate.of(s)
    val frontendMetadata = FrontendMetadataSurrogate.of(s)
    collector.encodeSerializableValue(
      ListSerializer(PolymorphicSerializer(MetaData::class)),
      s.metaList,
    )
    s.collecting = false
    return XcfaPayload(
      s.classNames,
      s.declNodes,
      s.exprNodes,
      s.stmtNodes,
      s.ctypeNodes,
      s.metaList,
      parseContext,
      frontendMetadata,
      surrogate,
    )
  }

  fun encodeToByteArray(format: BinaryFormat, xcfa: XCFA, parseContext: ParseContext): ByteArray {
    val s = XcfaSerializationSession(parseContext, decoding = false)
    return s.use {
      format.encodeToByteArray(XcfaPayload.serializer(), payload(s, xcfa, format.serializersModule))
    }
  }

  fun encodeToString(format: StringFormat, xcfa: XCFA, parseContext: ParseContext): String {
    val s = XcfaSerializationSession(parseContext, decoding = false)
    return s.use {
      format.encodeToString(XcfaPayload.serializer(), payload(s, xcfa, format.serializersModule))
    }
  }

  private fun finish(s: XcfaSerializationSession, payload: XcfaPayload): Pair<XCFA, ParseContext> {
    payload.parseContext.applyTo(s)
    payload.frontendMetadata.applyTo(s)
    return payload.xcfa.toXcfa() to s.parseContext
  }

  fun decodeFromByteArray(format: BinaryFormat, bytes: ByteArray): Pair<XCFA, ParseContext> {
    val s = XcfaSerializationSession(ParseContext(), decoding = true)
    return s.use { finish(s, format.decodeFromByteArray(XcfaPayload.serializer(), bytes)) }
  }

  fun decodeFromString(format: StringFormat, string: String): Pair<XCFA, ParseContext> {
    val s = XcfaSerializationSession(ParseContext(), decoding = true)
    return s.use { finish(s, format.decodeFromString(XcfaPayload.serializer(), string)) }
  }
}
