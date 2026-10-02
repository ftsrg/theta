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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.MemoryTypeKey
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.memoryTypeKey

private typealias ArrayType2D = ArrayType<out Type, ArrayType<out Type, out Type>>

/**
 * Converts dereferences to array expressions. The arrays are stored in global variables per type
 * (per combination of array type, offset type, and element type): there is a global array for each
 * such combination. A dereference like (deref array offset) is converted to arrays[array][offset],
 * where arrays is the global array variable corresponding to the types of array, offset, and
 * element. Upon each write to the memory location, the corresponding global array is also updated
 * to reflect the change.
 *
 * There is exactly ONE array per [MemoryTypeKey]: a finer, per-dereference partition is unsound,
 * because the same cell can be reached both through a global pointer variable and through its
 * constant-folded base literal, and the two dereferences would then read and write different
 * arrays. The array starts havoced -- stack and heap cells are garbage until written, and a
 * global's initialization is materialized as ordinary writes in the init procedure.
 */
class DereferenceToArrayPass : ProcedurePass {

  companion object {
    /** Zero every memory array; a decision-diagram fixpoint needs finite initial states. */
    var zeroInitialized: Boolean = false
  }

  private lateinit var arraysByType: Map<MemoryTypeKey, VarDecl<out ArrayType2D>>

  /** Returns an array from the pre-generated lookup of types */
  private val <A : Type, O : Type, T : Type> Dereference<A, O, T>.arrays:
    VarDecl<ArrayType<A, ArrayType<O, T>>>
    get() {
      val arrayType = ArrayType.of(array.type, ArrayType.of(offset.type, type))
      return cast(arraysByType[memoryTypeKey]!!, arrayType)
    }

  /** Creates arrays from dereference types */
  private fun createArray(key: MemoryTypeKey, xcfa: XcfaBuilder): VarDecl<out ArrayType2D> {
    val (derefArrayType, derefOffsetType, derefType) = key
    val arrayType = ArrayType.of(derefArrayType, ArrayType.of(derefOffsetType, derefType))

    val decl = Decls.Var("__arrays_${derefArrayType}_${derefOffsetType}_${derefType}", arrayType)
    val (globalDecl, initLabel) =
      if (zeroInitialized) {
        val defaultValue =
          ArrayLitExpr.of(
            listOf(),
            cast(arrayType.elemType.defaultValue, arrayType.elemType),
            arrayType,
          )
        XcfaGlobalVar(decl, defaultValue, atomic = true) to AssignStmtLabel(decl, defaultValue)
      } else {
        XcfaGlobalVar(decl, atomic = true) to StmtLabel(HavocStmt.of(decl))
      }
    xcfa.addVar(globalDecl)
    xcfa.getInitProcedures().forEach { (procedure, _) ->
      procedure.initLoc.outgoingEdges.toSet().forEach { edge ->
        procedure.removeEdge(edge)
        procedure.addEdge(edge.withLabel(SequenceLabel(listOf(initLabel, edge.label))))
      }
    }
    return decl as VarDecl<out ArrayType2D>
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!::arraysByType.isInitialized) {
      val arrays = mutableMapOf<MemoryTypeKey, VarDecl<out ArrayType2D>>()
      val types = mutableSetOf<MemoryTypeKey>()
      builder.parent.getProcedures().forEach { p ->
        p.getEdges().forEach { e ->
          e.label.dereferences.forEach { deref -> types.add(deref.memoryTypeKey) }
        }
      }
      types.forEach { arrays[it] = createArray(it, builder.parent) }
      arraysByType = arrays
    }

    // Only the first edge of an init procedure that nothing loops back to runs before any other
    // write to memory, so only there may a whole row be overwritten (see [zeroWholeRows]).
    val firstEdges =
      if (
        builder.parent.getInitProcedures().any { it.first === builder } &&
          builder.initLoc.incomingEdges.isEmpty()
      )
        builder.initLoc.outgoingEdges.toSet()
      else emptySet()
    builder.getEdges().toList().forEach { edge ->
      val label = if (edge in firstEdges) edge.label.zeroWholeRows() else edge.label
      val newLabel = label.replaceDereferences(builder.parent)
      if (newLabel != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  /**
   * A global object without an initializer is zeroed one cell at a time, one store per cell, so a
   * large global array gives a long chain of nested array writes. Here the default-valued stores to
   * one object are replaced by one store of a constant default row: `arrays[b] := const(0)`.
   *
   * Only cells that no store names change: they were unconstrained and now read the default. In the
   * object that is what C gives a global anyway; outside it, a read is out of bounds.
   *
   * A row qualifies only if nothing on this edge could see the difference:
   * - its base is a literal and not the default (the flat models put all memory at base 0);
   * - every other access of its array (same [MemoryTypeKey]) comes after its last store: a read, a
   *   store through a symbolic address, or a conditional store could otherwise meet the row;
   * - its stores are plain, directly in a sequence, at distinct literal offsets, so no default
   *   store is needed to undo an earlier one.
   *
   * The row store takes the place of the first store to the row; the other stores stay in order.
   */
  private fun XcfaLabel.zeroWholeRows(): XcfaLabel {
    val items = flatSequence()
    val plain = mutableListOf<IndexedValue<MemoryAssignStmt<*, *, *>>>()
    val firstOther = mutableMapOf<MemoryTypeKey, Int>()
    items.forEachIndexed { index, item ->
      val store = (item as? StmtLabel)?.stmt as? MemoryAssignStmt<*, *, *>
      val others =
        if (store != null && store.isPlain()) {
          plain.add(IndexedValue(index, store))
          store.expr.dereferences
        } else item.allDereferences()
      others.forEach { firstOther.putIfAbsent(it.memoryTypeKey, index) }
    }
    val rows =
      plain
        .groupBy { it.value.deref.memoryTypeKey to it.value.deref.array }
        .values
        .filter { row ->
          val key = row.first().value.deref.memoryTypeKey
          val stores = row.map { it.value }
          row.last().index < (firstOther[key] ?: Int.MAX_VALUE) &&
            stores.map { it.deref.offset }.toSet().size == stores.size &&
            stores.count { it.isDefault() } >= 2
        }
        .map { row -> row.map { it.value } }
    if (rows.isEmpty()) return this
    return replaceStores(
      rows.map { it.first() }.toIdentitySet(),
      rows.flatMap { row -> row.filter { it.isDefault() } }.toIdentitySet(),
    )
  }

  private fun MemoryAssignStmt<*, *, *>.isPlain() =
    deref.array is LitExpr<*> &&
      deref.array != deref.array.type.defaultValue &&
      deref.offset is LitExpr<*>

  private fun MemoryAssignStmt<*, *, *>.isDefault() = expr == deref.type.defaultValue

  private fun <T> Collection<T>.toIdentitySet(): Set<T> =
    java.util.Collections.newSetFromMap(java.util.IdentityHashMap<T, Boolean>()).also {
      it.addAll(this)
    }

  /** The labels of (nested) sequences, in execution order. */
  private fun XcfaLabel.flatSequence(): List<XcfaLabel> =
    if (this is SequenceLabel) labels.flatMap { it.flatSequence() } else listOf(this)

  /** Every dereference in the label, also the ones in a return. */
  private fun XcfaLabel.allDereferences(): List<Dereference<*, *, *>> =
    when (this) {
      is SequenceLabel -> labels.flatMap { it.allDereferences() }
      is NondetLabel -> labels.flatMap { it.allDereferences() }
      is ReturnLabel -> enclosedLabel.allDereferences()
      else -> dereferences
    }

  private fun XcfaLabel.replaceStores(
    first: Set<MemoryAssignStmt<*, *, *>>,
    dropped: Set<MemoryAssignStmt<*, *, *>>,
  ): XcfaLabel =
    when (this) {
      is SequenceLabel ->
        SequenceLabel(
          labels.flatMap { label ->
            val store = (label as? StmtLabel)?.stmt as? MemoryAssignStmt<*, *, *>
            when {
              store == null -> listOf(label.replaceStores(first, dropped))
              store in first ->
                listOfNotNull(
                  StmtLabel(defaultRow(store.deref), metadata = label.metadata),
                  label.takeUnless { store in dropped },
                )
              store in dropped -> emptyList()
              else -> listOf(label)
            }
          },
          metadata,
        )
      else -> this
    }

  /** `arrays[base] := const(default)` for the row of [deref]. */
  private fun defaultRow(deref: Dereference<*, *, *>): AssignStmt<*> {
    val arrayType = ArrayType.of(deref.array.type, ArrayType.of(deref.offset.type, deref.type))
    val arrays = deref.arrays
    val row =
      ArrayLitExpr.of(listOf(), cast(deref.type.defaultValue, deref.type), arrayType.elemType)
    return AssignStmt.of(
      cast(arrays, arrayType),
      cast(
        ArrayWriteExpr.of(
          cast(arrays.ref, arrayType),
          cast(deref.array, arrayType.indexType),
          cast(row, arrayType.elemType),
        ),
        arrayType,
      ),
    )
  }

  private fun XcfaLabel.replaceDereferences(xcfa: XcfaBuilder): XcfaLabel {
    return when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.replaceDereferences(xcfa) })
      is NondetLabel -> NondetLabel(labels.map { it.replaceDereferences(xcfa) }.toSet())
      is StmtLabel -> {
        StmtLabel(
          when (stmt) {
            is MemoryAssignStmt<*, *, *> -> {
              // (deref array offset) := expr  -> arrays[array][offset] := expr
              // -> Assign(
              //      arrays,
              //      ArrayWrite(arrays, array, ArrayWrite(ArrayRead(arrays, array), offset, expr))
              //    )
              val deref = stmt.deref
              val arrayType =
                ArrayType.of(deref.array.type, ArrayType.of(deref.offset.type, deref.type))
              val arrays = deref.arrays
              AssignStmt.of(
                cast(arrays, arrayType),
                cast(
                  ArrayWriteExpr.of(
                    cast(arrays.ref, arrayType),
                    cast(deref.array.getArrayReads(xcfa), arrayType.indexType),
                    ArrayWriteExpr.of(
                      cast(
                        ArrayReadExpr.of(
                          cast(arrays.ref, arrayType),
                          cast(deref.array.getArrayReads(xcfa), arrayType.indexType),
                        ),
                        arrayType.elemType,
                      ),
                      cast(deref.offset.getArrayReads(xcfa), arrayType.elemType.indexType),
                      cast(stmt.expr.getArrayReads(xcfa), arrayType.elemType.elemType),
                    ),
                  ),
                  arrayType,
                ),
              )
            }

            is AssignStmt<*> ->
              AssignStmt.of(
                cast(stmt.varDecl, stmt.varDecl.type),
                cast(stmt.expr.getArrayReads(xcfa), stmt.varDecl.type),
              )

            is AssumeStmt -> AssumeStmt.of(stmt.cond.getArrayReads(xcfa))

            else -> stmt
          },
          choiceType,
          metadata,
        )
      }

      is InvokeLabel ->
        InvokeLabel(
          name,
          params.map { it.getArrayReads(xcfa) },
          metadata,
          tempLookup,
          isLibraryFunction,
        )

      is StartLabel ->
        StartLabel(name, params.map { it.getArrayReads(xcfa) }, pidVar, metadata, tempLookup)

      is ReturnLabel -> ReturnLabel(enclosedLabel.replaceDereferences(xcfa))
      else -> this
    }
  }

  private fun <T : Type> Expr<T>.getArrayReads(xcfa: XcfaBuilder): Expr<T> =
    if (this is Dereference<*, *, *>) {
      val arrayType = ArrayType.of(this.array.type, ArrayType.of(this.offset.type, this.type))
      // (deref array offset) -> arrays[array][offset]
      // -> ArrayRead(ArrayRead(arrays, array), offset)
      ArrayReadExpr.of(
        ArrayReadExpr.of(
          cast(this.arrays.ref, arrayType),
          cast(this.array.getArrayReads(xcfa), this.array.type),
        ),
        cast(this.offset.getArrayReads(xcfa), this.offset.type),
      ) as Expr<T>
    } else {
      withOps(ops.map { it.getArrayReads(xcfa) })
    }
}
