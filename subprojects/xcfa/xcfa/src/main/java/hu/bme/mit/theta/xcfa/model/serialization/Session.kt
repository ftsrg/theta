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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
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
import kotlinx.serialization.encoding.AbstractEncoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.modules.SerializersModule

/**
 * Identity tables shared by the serializers of one encode or decode.
 *
 * Declarations, expressions, statements, C types, metadata and locations have identity (a [VarDecl]
 * is equal only to itself, C types are keyed by expression identity, edges point at location
 * objects), so they are written once into a table and referred to by index. Encoding runs twice
 * over the same object: the first pass only fills the tables, the second writes them out before
 * anything that refers to them, so decoding can resolve every reference on the spot.
 */
class XcfaSerializationSession
internal constructor(internal val parseContext: ParseContext, internal val decoding: Boolean) {

  /** While true (first encoding pass), unseen objects are added; afterwards they are an error. */
  internal var collecting = !decoding

  private val declIds = IdentityHashMap<Decl<*>, Int>()
  private val exprIds = IdentityHashMap<Expr<*>, Int>()
  private val stmtIds = IdentityHashMap<Stmt, Int>()
  private val ctypeIds = IdentityHashMap<CComplexType, Int>()
  private val ctypeNodeIds = HashMap<CTypeNode, Int>()
  private val metaIds = IdentityHashMap<MetaData, Int>()
  private val locIds = IdentityHashMap<XcfaLocation, Int>()
  private val classIds = HashMap<String, Int>()

  internal val declNodes = ArrayList<DeclNode>()
  internal val exprNodes = ArrayList<ExprNode>()
  internal val stmtNodes = ArrayList<StmtNode>()
  internal val ctypeNodes = ArrayList<CTypeNode>()
  internal val metaList = ArrayList<MetaData>()
  internal val classNames = ArrayList<String>()

  internal val decls = ArrayList<Decl<*>>()
  internal val exprs = ArrayList<Expr<*>>()
  internal val stmts = ArrayList<Stmt>()
  internal val ctypes = ArrayList<CComplexType>()
  internal val metas = ArrayList<MetaData>()
  internal val locs = ArrayList<XcfaLocation>()
  internal val classes = ArrayList<Class<*>>()

  internal fun reachableExprs(): Map<Expr<*>, Int> = exprIds

  internal fun reachableDecls(): Map<Decl<*>, Int> = declIds

  internal fun reachableStmts(): Map<Stmt, Int> = stmtIds

  private fun <K> intern(ids: IdentityHashMap<K, Int>, key: K, create: () -> Unit): Int {
    ids[key]?.let {
      return it
    }
    check(collecting) { "Not collected in the first pass: ${key!!::class.java.name} $key" }
    create()
    // create() may have registered children first, so the id is assigned only now.
    return ids.size.also { ids[key] = it }
  }

  internal fun classId(cls: Class<*>): Int =
    classIds.getOrPut(cls.name) {
      check(collecting) { "Not collected in the first pass: class ${cls.name}" }
      classNames.add(cls.name)
      classNames.size - 1
    }

  internal fun declId(d: Decl<*>): Int = intern(declIds, d) { declNodes.add(DeclNode.of(d)) }

  internal fun exprId(e: Expr<*>): Int =
    intern(exprIds, e) {
      val node = ExprNode.of(e, this)
      exprNodes.add(node)
    }

  internal fun stmtId(s: Stmt): Int = intern(stmtIds, s) { stmtNodes.add(StmtNode.of(s, this)) }

  // C types are hash-consed: the parser re-expands struct types on every use, so the same type
  // exists as thousands of objects. Nothing keys on their identity (equality is structural).
  internal fun ctypeId(t: CComplexType): Int =
    ctypeIds[t]
      ?: run {
        check(collecting) { "Not collected in the first pass: C type $t" }
        val node = CTypeNode.of(t, this)
        val id =
          ctypeNodeIds.getOrPut(node) {
            ctypeNodes.add(node)
            ctypeNodes.size - 1
          }
        id.also { ctypeIds[t] = it }
      }

  internal fun metaId(m: MetaData): Int =
    if (m === EmptyMetaData) -1 else intern(metaIds, m) { metaList.add(m) }

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
        return block()
      } finally {
        current.remove()
      }
    }
  }
}

private fun session() = XcfaSerializationSession.get()

private fun intDescriptor(name: String) = PrimitiveSerialDescriptor(name, PrimitiveKind.INT)

object ExprReferenceSerializer : KSerializer<Expr<*>> {
  override val descriptor = intDescriptor("theta.ExprRef")

  override fun serialize(encoder: Encoder, value: Expr<*>) =
    encoder.encodeInt(session().exprId(value))

  override fun deserialize(decoder: Decoder): Expr<*> = session().exprs[decoder.decodeInt()]
}

@Suppress("UNCHECKED_CAST")
object BoolExprReferenceSerializer : KSerializer<Expr<BoolType>> {
  override val descriptor = intDescriptor("theta.BoolExprRef")

  override fun serialize(encoder: Encoder, value: Expr<BoolType>) =
    encoder.encodeInt(session().exprId(value))

  override fun deserialize(decoder: Decoder): Expr<BoolType> =
    session().exprs[decoder.decodeInt()] as Expr<BoolType>
}

object LitExprReferenceSerializer : KSerializer<LitExpr<*>> {
  override val descriptor = intDescriptor("theta.LitExprRef")

  override fun serialize(encoder: Encoder, value: LitExpr<*>) =
    encoder.encodeInt(session().exprId(value))

  override fun deserialize(decoder: Decoder): LitExpr<*> =
    session().exprs[decoder.decodeInt()] as LitExpr<*>
}

object VarDeclReferenceSerializer : KSerializer<VarDecl<*>> {
  override val descriptor = intDescriptor("theta.VarDeclRef")

  override fun serialize(encoder: Encoder, value: VarDecl<*>) =
    encoder.encodeInt(session().declId(value))

  override fun deserialize(decoder: Decoder): VarDecl<*> =
    session().decls[decoder.decodeInt()] as VarDecl<*>
}

object StmtReferenceSerializer : KSerializer<Stmt> {
  override val descriptor = intDescriptor("theta.StmtRef")

  override fun serialize(encoder: Encoder, value: Stmt) = encoder.encodeInt(session().stmtId(value))

  override fun deserialize(decoder: Decoder): Stmt = session().stmts[decoder.decodeInt()]
}

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

/** Runs serializers without producing output: the first encoding pass. */
@OptIn(ExperimentalSerializationApi::class)
internal class CollectingEncoder(override val serializersModule: SerializersModule) :
  AbstractEncoder() {
  override fun encodeValue(value: Any) {}

  override fun encodeNull() {}
}
