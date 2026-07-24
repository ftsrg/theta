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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.TypeUtils.getDefaultValue
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*

/**
 * Collapses the 2-D `(base, offset)` address of every dereference into a single flat address, as if
 * every object's base were 0: `(deref base offset t)` becomes `(deref 0 (+ base offset) t)`.
 *
 * This is the second half of the [MemoryModelType.flat] model. The first half lives at object
 * creation: an object's base value is minted as `id * `[FLAT_STRIDE] (see [flatBaseValue]) rather
 * than a small consecutive id, so each object owns a disjoint `[id*STRIDE, id*STRIDE + STRIDE)`
 * slice of the one address line and `base + offset` never collides across objects (as long as no
 * object is larger than [FLAT_STRIDE] cells). Because a pointer is then a single scalar address
 * (`base + offset` folded together), storing one into a memory cell needs no duplication -- the
 * offset rides along inside the value -- which is the whole point of the flat model.
 *
 * Folding here, downstream of [ReferenceElimination], means every memory backend (the monolithic
 * [DereferenceToArrayPass], the ordering-consistency event graph, the CEGAR pointer analysis) sees
 * addresses already normalized to a single scalar, so two syntactically different `(base, offset)`
 * pairs that name the same cell -- `a[j]` as `(deref A j)` and `p = &a[j]; *p` as `(deref A+j 0)` --
 * alias correctly without any per-backend change.
 */
class FlatMemoryPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {

    /**
     * Width of each object's slice of the flat address line. An object's base is `id * FLAT_STRIDE`
     * and its cells occupy offsets `0 until size`, so this bounds the largest addressable object
     * (and, together with the pointer width under bitvector arithmetic, the number of objects).
     */
    const val FLAT_STRIDE: Long = 1L shl 16

    /**
     * The base value to mint for the object with raw id [rawId]: spaced by [FLAT_STRIDE] under the
     * flat model, the bare id otherwise. Returned as a decimal string for `CComplexType.getValue`,
     * which types it for the decided arithmetic.
     */
    fun flatBaseValue(rawId: Int, parseContext: ParseContext): String =
      if (parseContext.memoryModel == MemoryModelType.flat) {
        (rawId.toLong() * FLAT_STRIDE).toString()
      } else {
        rawId.toString()
      }

    /**
     * Spaces a *runtime* base id (the `alloca`/`malloc` counter value, not a compile-time constant)
     * onto the flat address line under the flat model: `rawBase` becomes `rawBase * `[FLAT_STRIDE].
     * The residue class of `rawBase` (mod 3: heap / alloca / address-taken) survives division by the
     * stride, so the memsafety partitioning still recovers it as `base / FLAT_STRIDE`. A no-op under
     * the multi model.
     */
    fun <T : Type> flatBaseExpr(
      rawBase: Expr<T>,
      retType: CComplexType,
      parseContext: ParseContext,
    ): Expr<T> =
      if (parseContext.memoryModel == MemoryModelType.flat) {
        cast(Mul(rawBase, cast(retType.getValue(FLAT_STRIDE.toString()), rawBase.type)), rawBase.type)
      } else {
        rawBase
      }
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (parseContext.memoryModel != MemoryModelType.flat) return builder

    builder.getEdges().toList().forEach { edge ->
      val newLabel = edge.label.foldFlat()
      if (newLabel != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  private fun XcfaLabel.foldFlat(): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.foldFlat() }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.foldFlat() }.toSet(), metadata)
      is StmtLabel ->
        StmtLabel(
          when (stmt) {
            is MemoryAssignStmt<*, *, *> -> foldMemoryAssign(stmt)
            is AssignStmt<*> ->
              AssignStmt.of(
                cast(stmt.varDecl, stmt.varDecl.type),
                cast(stmt.expr.foldFlat(), stmt.varDecl.type),
              )
            is AssumeStmt -> AssumeStmt.of(stmt.cond.foldFlat())
            else -> stmt
          },
          choiceType,
          metadata,
        )

      is InvokeLabel ->
        InvokeLabel(name, params.map { it.foldFlat() }, metadata, tempLookup, isLibraryFunction)

      is StartLabel ->
        StartLabel(name, params.map { it.foldFlat() }, pidVar, metadata, tempLookup)

      is ReturnLabel -> ReturnLabel(enclosedLabel.foldFlat())
      else -> this
    }

  @Suppress("UNCHECKED_CAST")
  private fun foldMemoryAssign(stmt: MemoryAssignStmt<*, *, *>): MemoryAssignStmt<*, *, *> =
    buildMemoryAssign(stmt.deref.foldFlat() as Dereference<*, *, *>, stmt.expr.foldFlat())

  private fun <P : Type, O : Type, D : Type> buildMemoryAssign(
    deref: Dereference<P, O, D>,
    expr: Expr<*>,
  ): MemoryAssignStmt<P, O, D> = MemoryAssignStmt.create(deref, cast(expr, deref.type))

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.foldFlat(): Expr<T> =
    if (this is Dereference<*, *, *>) {
      val foldedArray = array.foldFlat()
      val foldedOffset = offset.foldFlat()
      val baseType = foldedArray.type
      val flatIndex = Add(cast(foldedArray, baseType), cast(foldedOffset, baseType))
      Dereference.of(getDefaultValue(baseType), cast(flatIndex, baseType), type) as Expr<T>
    } else {
      withOps(ops.map { it.foldFlat() })
    }
}
