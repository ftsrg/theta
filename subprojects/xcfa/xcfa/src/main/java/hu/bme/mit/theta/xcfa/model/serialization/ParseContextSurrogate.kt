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

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.CStmtCounter
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import java.lang.reflect.Field
import java.lang.reflect.Modifier
import java.math.BigInteger
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

// ParseContext keeps much of its state in private fields without accessors; the experiment reads
// and restores them reflectively. The coverage test pins the field list.
private fun Class<*>.instanceFields(): Map<String, Field> =
  declaredFields
    .filter { !Modifier.isStatic(it.modifiers) }
    .onEach { it.isAccessible = true }
    .associateBy { it.name }

private val PARSE_CONTEXT_FIELDS = ParseContext::class.java.instanceFields()
private val COUNTER_FIELDS = CStmtCounter::class.java.instanceFields()
private val METADATA_FIELDS = FrontendMetadata::class.java.instanceFields()

@Serializable
data class ParseContextSurrogate(
  val arithmeticTraits: List<String>,
  val architecture: String,
  val multiThreading: Boolean,
  val arithmetic: String,
  val arithmeticAutoSelected: Boolean,
  val signedWraparound: Boolean,
  val memoryModel: String,
  val checkMemsafety: Boolean,
  val everyMemberAccessed: Boolean,
  val cStmtCounter: Map<String, Int>,
  val fullyAtomicObjects: List<String>,
  val staticUnions: List<String>,
  val sourceTraits: Map<String, Int>,
  val atomicObjectCells: Map<String, List<Int>>,
  val subObjectCells: Map<String, Map<Int, String>>,
  val staticObjectParents: List<Pair<String, String?>>,
  /** Keys are indices into the C type table. */
  val accessedMembers: List<Pair<Int, List<String>>>,
) {

  @Suppress("UNCHECKED_CAST")
  fun applyTo(s: XcfaSerializationSession) {
    val pc = s.parseContext
    fun <T> get(name: String) = PARSE_CONTEXT_FIELDS.getValue(name).get(pc) as T
    fun set(name: String, value: Any?) = PARSE_CONTEXT_FIELDS.getValue(name).set(pc, value)
    fun enumOf(name: String, value: String) =
      PARSE_CONTEXT_FIELDS.getValue(name).type.enumConstants.first { (it as Enum<*>).name == value }

    set("arithmeticTraits", arithmeticTraits.mapTo(LinkedHashSet()) { ArithmeticTrait.valueOf(it) })
    set("architecture", enumOf("architecture", architecture))
    set("multiThreading", multiThreading)
    set("arithmetic", enumOf("arithmetic", arithmetic))
    set("arithmeticAutoSelected", arithmeticAutoSelected)
    set("signedWraparound", signedWraparound)
    set("memoryModel", enumOf("memoryModel", memoryModel))
    set("checkMemsafety", checkMemsafety)
    set("everyMemberAccessed", everyMemberAccessed)
    val counter = get<CStmtCounter>("cStmtCounter")
    cStmtCounter.forEach { (k, v) -> COUNTER_FIELDS.getValue(k).setInt(counter, v) }
    get<MutableSet<BigInteger>>("fullyAtomicObjects").addAll(fullyAtomicObjects.map(::BigInteger))
    get<MutableSet<BigInteger>>("staticUnions").addAll(staticUnions.map(::BigInteger))
    set("sourceTraits", LinkedHashMap(sourceTraits))
    get<MutableMap<BigInteger, MutableSet<Int>>>("atomicObjectCells")
      .putAll(atomicObjectCells.map { (k, v) -> BigInteger(k) to LinkedHashSet(v) })
    get<MutableMap<BigInteger, MutableMap<Int, BigInteger>>>("subObjectCells")
      .putAll(
        subObjectCells.map { (k, v) ->
          BigInteger(k) to v.mapValuesTo(LinkedHashMap()) { BigInteger(it.value) }
        }
      )
    get<MutableMap<BigInteger, BigInteger?>>("staticObjectParents")
      .putAll(staticObjectParents.map { (k, v) -> BigInteger(k) to v?.let(::BigInteger) })
    get<MutableMap<CStruct, MutableSet<String>>>("accessedMembers")
      .putAll(accessedMembers.map { (k, v) -> s.ctypes[k] as CStruct to LinkedHashSet(v) })
  }

  companion object {

    /** ParseContext fields this surrogate stores; `metadata` is [FrontendMetadataSurrogate]. */
    val COVERED =
      setOf(
        "metadata",
        "arithmeticTraits",
        "architecture",
        "multiThreading",
        "arithmetic",
        "arithmeticAutoSelected",
        "signedWraparound",
        "memoryModel",
        "checkMemsafety",
        "everyMemberAccessed",
        "cStmtCounter",
        "fullyAtomicObjects",
        "staticUnions",
        "sourceTraits",
        "atomicObjectCells",
        "subObjectCells",
        "staticObjectParents",
        "accessedMembers",
      )

    @Suppress("UNCHECKED_CAST")
    fun of(s: XcfaSerializationSession): ParseContextSurrogate {
      val pc = s.parseContext
      fun <T> get(name: String) = PARSE_CONTEXT_FIELDS.getValue(name).get(pc) as T
      val counter = get<CStmtCounter>("cStmtCounter")
      return ParseContextSurrogate(
        arithmeticTraits = get<Set<Enum<*>>>("arithmeticTraits").map { it.name },
        architecture = get<Enum<*>>("architecture").name,
        multiThreading = get("multiThreading"),
        arithmetic = get<Enum<*>>("arithmetic").name,
        arithmeticAutoSelected = get("arithmeticAutoSelected"),
        signedWraparound = get("signedWraparound"),
        memoryModel = get<Enum<*>>("memoryModel").name,
        checkMemsafety = get("checkMemsafety"),
        everyMemberAccessed = get("everyMemberAccessed"),
        cStmtCounter = COUNTER_FIELDS.mapValues { it.value.getInt(counter) },
        fullyAtomicObjects = get<Set<BigInteger>>("fullyAtomicObjects").map { it.toString() },
        staticUnions = get<Set<BigInteger>>("staticUnions").map { it.toString() },
        sourceTraits = LinkedHashMap(get<Map<String, Int>>("sourceTraits")),
        atomicObjectCells =
          get<Map<BigInteger, Set<Int>>>("atomicObjectCells")
            .map { (k, v) -> k.toString() to v.toList() }
            .toMap(LinkedHashMap()),
        subObjectCells =
          get<Map<BigInteger, Map<Int, BigInteger>>>("subObjectCells")
            .map { (k, v) -> k.toString() to v.mapValues { it.value.toString() } }
            .toMap(LinkedHashMap()),
        staticObjectParents =
          get<Map<BigInteger, BigInteger?>>("staticObjectParents").map { (k, v) ->
            k.toString() to v?.toString()
          },
        accessedMembers =
          get<Map<CStruct, Set<String>>>("accessedMembers").map { (k, v) ->
            s.ctypeId(k) to v.toList()
          },
      )
    }
  }
}

/**
 * [FrontendMetadata] is keyed by object identity (C types of expressions, and identity hashes for
 * non-string owners), so it can only be carried over for objects the XCFA still reaches; those are
 * re-keyed to their rebuilt counterparts. Entries of string owners keep their key. Entries of
 * unreachable objects are dropped: in another process their identity hash would be reused by an
 * unrelated object.
 */
@Serializable
data class FrontendMetadataSurrogate(
  /** Pairs of (expression index, C type index). */
  val cTypes: List<Pair<Int, Int>>,
  val entries: List<Entry>,
) {

  @Serializable
  sealed class Owner {
    /** String.hashCode() of a string owner. */
    @Serializable @SerialName("string") data class StringKey(val key: Int) : Owner()

    @Serializable @SerialName("expr") data class Expr(val index: Int) : Owner()

    @Serializable @SerialName("decl") data class Decl(val index: Int) : Owner()

    @Serializable @SerialName("stmt") data class Stmt(val index: Int) : Owner()
  }

  @Serializable
  sealed class Value {
    @Serializable @SerialName("string") data class Str(val value: String) : Value()

    @Serializable @SerialName("bool") data class Bool(val value: Boolean) : Value()

    @Serializable @SerialName("int") data class IntValue(val value: Int) : Value()

    @Serializable @SerialName("ctype") data class CType(val index: Int) : Value()

    @Serializable @SerialName("expr") data class ExprValue(val index: Int) : Value()
  }

  @Serializable data class Entry(val owner: Owner, val values: Map<String, Value>)

  @Suppress("UNCHECKED_CAST")
  fun applyTo(s: XcfaSerializationSession) {
    val metadata = s.parseContext.metadata
    cTypes.forEach { (e, t) -> metadata.create(s.exprs[e], "cType", s.ctypes[t]) }
    val lookup =
      METADATA_FIELDS.getValue("lookupKeyValue").get(metadata)
        as MutableMap<Int, MutableMap<String, Any>>
    val stringKeys = METADATA_FIELDS.getValue("stringKeys").get(metadata) as MutableSet<Int>
    for (entry in entries) {
      val key =
        when (val o = entry.owner) {
          is Owner.StringKey -> o.key.also { stringKeys.add(it) }
          is Owner.Expr -> System.identityHashCode(s.exprs[o.index])
          is Owner.Decl -> System.identityHashCode(s.decls[o.index])
          is Owner.Stmt -> System.identityHashCode(s.stmts[o.index])
        }
      val values = lookup.getOrPut(key) { LinkedHashMap() }
      entry.values.forEach { (k, v) ->
        values[k] =
          when (v) {
            is Value.Str -> v.value
            is Value.Bool -> v.value
            is Value.IntValue -> v.value
            is Value.CType -> s.ctypes[v.index]
            is Value.ExprValue -> s.exprs[v.index]
          }
      }
    }
  }

  companion object {

    val COVERED = setOf("types", "lookupKeyValue", "stringKeys")

    /**
     * Value types left out on purpose: the declaration-side C types the parser records for named
     * owners are only read while parsing.
     */
    val DROPPED_VALUE_TYPES: Set<Class<*>> = setOf(CSimpleType::class.java)

    /** Must run after everything else was collected: only reachable objects are kept. */
    @Suppress("UNCHECKED_CAST")
    fun of(s: XcfaSerializationSession): FrontendMetadataSurrogate {
      val metadata = s.parseContext.metadata
      val types =
        METADATA_FIELDS.getValue("types").get(metadata) as Map<Tuple2<Expr<*>, Int>, CComplexType>
      val reachableExprs = s.reachableExprs()
      val reachableDecls = s.reachableDecls()
      val cTypes = ArrayList<Pair<Int, Int>>()
      for ((key, type) in types) {
        val e = key.get1()
        val reachable =
          reachableExprs.containsKey(e) ||
            (e is RefExpr<*> && e === e.decl.ref && reachableDecls.containsKey(e.decl))
        if (reachable) cTypes.add(s.exprId(e) to s.ctypeId(type))
      }

      val owners = HashMap<Int, Owner>()
      s.reachableExprs().forEach { (e, i) ->
        owners.putIfAbsent(System.identityHashCode(e), Owner.Expr(i))
      }
      s.reachableDecls().forEach { (d, i) ->
        owners.putIfAbsent(System.identityHashCode(d), Owner.Decl(i))
      }
      s.reachableStmts().forEach { (st, i) ->
        owners.putIfAbsent(System.identityHashCode(st), Owner.Stmt(i))
      }

      val lookup =
        METADATA_FIELDS.getValue("lookupKeyValue").get(metadata) as Map<Int, Map<String, Any>>
      val stringKeys = METADATA_FIELDS.getValue("stringKeys").get(metadata) as Set<Int>
      val entries = ArrayList<Entry>()
      for ((key, values) in lookup) {
        val owner = if (key in stringKeys) Owner.StringKey(key) else owners[key] ?: continue
        val kept = LinkedHashMap<String, Value>()
        for ((k, v) in values) {
          kept[k] =
            when (v) {
              is String -> Value.Str(v)
              is Boolean -> Value.Bool(v)
              is Int -> Value.IntValue(v)
              is CComplexType -> Value.CType(s.ctypeId(v))
              is Expr<*> -> Value.ExprValue(s.exprId(v))
              else -> {
                check(DROPPED_VALUE_TYPES.any { it.isInstance(v) }) {
                  "Frontend metadata '$k' has a value of unsupported type ${v.javaClass.name}"
                }
                continue
              }
            }
        }
        if (kept.isNotEmpty()) entries.add(Entry(owner, kept))
      }
      return FrontendMetadataSurrogate(cTypes, entries)
    }
  }
}
