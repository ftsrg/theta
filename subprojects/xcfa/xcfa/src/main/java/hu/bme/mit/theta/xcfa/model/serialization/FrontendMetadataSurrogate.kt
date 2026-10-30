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
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * [FrontendMetadata] is keyed by the identity hashes of non-string owners, so it can only be
 * carried over for objects the XCFA still reaches; those are re-keyed to their rebuilt
 * counterparts. Entries of string owners keep their key. Entries of unreachable objects are
 * dropped: in another process their identity hash would be reused by an unrelated object.
 */
@Serializable
data class FrontendMetadataSurrogate(val entries: List<Entry>) {

  @Serializable
  sealed class Owner {
    /** String.hashCode() of a string owner. */
    @Serializable @SerialName("string") data class StringKey(val key: Int) : Owner()

    /** An expression, declaration or statement: an index into the object table. */
    @Serializable @SerialName("object") data class Object(val index: Int) : Owner()
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

  fun applyTo(s: XcfaSerializationSession) {
    val metadata = s.parseContext.metadata
    for (entry in entries) {
      val key =
        when (val o = entry.owner) {
          is Owner.StringKey -> o.key
          is Owner.Object -> System.identityHashCode(s.objects.valueAt(o.index))
        }
      val values =
        entry.values.mapValues { (_, v) ->
          when (v) {
            is Value.Str -> v.value
            is Value.Bool -> v.value
            is Value.IntValue -> v.value
            is Value.CType -> s.ctype(v.index)
            is Value.ExprValue -> s.expr(v.index)
          }
        }
      metadata.restore(key, entry.owner is Owner.StringKey, values)
    }
  }

  companion object {

    val COVERED = setOf("lookupKeyValue", "stringKeys")

    /**
     * Value types left out on purpose: the declaration-side C types the parser records for named
     * owners are only read while parsing.
     */
    val DROPPED_VALUE_TYPES: Set<Class<*>> = setOf(CSimpleType::class.java)

    /** Must run after everything else was collected: only reachable objects are kept. */
    fun of(s: XcfaSerializationSession): FrontendMetadataSurrogate {
      val metadata = s.parseContext.metadata
      val owners = HashMap<Int, Owner>()
      s.objects.values.forEachIndexed { i, v ->
        if (v is Expr<*> || v is Decl<*> || v is Stmt) {
          owners.putIfAbsent(System.identityHashCode(v), Owner.Object(i))
        }
      }

      val lookup = metadata.lookupKeyValue
      val stringKeys = metadata.stringKeys
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
      return FrontendMetadataSurrogate(entries)
    }
  }
}
