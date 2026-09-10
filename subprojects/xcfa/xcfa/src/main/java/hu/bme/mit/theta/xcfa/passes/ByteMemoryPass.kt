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
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ByteUnionSlice
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger

/**
 * The second half of the
 * [hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType.bytes] model: every
 * memory cell is one byte. It rewrites each wide dereference into the little-endian `Concat` of the
 * one-byte cells at its own byte offset, and each wide memory *write* into a per-byte
 * `Extract`-and-store -- so that after this pass every `(deref … Bv8)` reaching a backend names a
 * single byte, and two differently-typed views of the same storage (an `int` and the `char`s
 * overlapping it, a union member and its byte array) land in the one `Bv8` array and alias.
 *
 * The frontend has already emitted **byte** offsets under the bytes model (subscripts scaled by the
 * element's byte size, struct members at their real `offsetof`, pointer arithmetic scaled by the
 * pointee's byte size), so this pass adds only the byte-splitting; it does no scaling of its own.
 * It runs downstream of [ReferenceElimination] and [FlatMemoryPass], so the derefs those introduce
 * (an address-taken local, a folded flat address) are byte-split here too, uniformly with the
 * frontend's own.
 *
 * A **floating-point** cell is REFUSED, loudly. Splitting one means routing the value through its
 * IEEE-754 encoding, and that conversion cannot be trusted: SMT-LIB's FloatingPoint sort has a
 * single NaN element, so `fp.to_ieee_bv` collapses every NaN to one bit pattern, and the theory
 * does not fix *which* -- measured against z3 4.12.6, a NaN's bits may differ from the canonical
 * pattern (sat), two NaNs must share their bits (unsat), and a payload round trip may lose the
 * payload (sat) or keep it (sat). In a verification query the solver picks whichever falsifies the
 * property, so a program inspecting a NaN's bits gets a spurious counterexample: a wrong `false`,
 * worth -16 where a refusal is worth 0.
 *
 * Leaving the float in an array of its own -- what this pass used to do -- is worse than refusing,
 * because it is silent: a `double` and the bytes overlapping it become unrelated storage, so
 * `u.value = 1.0; u.parts.msw` reads cells nothing ever wrote and returns an unconstrained value.
 * Refusing says the same thing out loud.
 *
 * A cell whose element type is neither of those is left untouched: a byte (`Bv8`) is already a
 * single cell. Byte splitting is a bitvector operation, so the model presumes bitvector arithmetic;
 * an `IntType` cell (integer arithmetic) has no fixed width and is likewise left alone.
 */
class ByteMemoryPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!parseContext.memoryModel.byteAddressed()) return builder

    builder.getEdges().toList().forEach { edge ->
      val newLabel = edge.label.bytify()
      if (newLabel != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  /** The width in bytes of a cell this pass splits, or null if it leaves the cell alone. */
  private fun byteWidth(type: Type): Int? {
    val bits =
      when (type) {
        is BvType -> type.size
        // Reached for any float that lives in memory under this model: refuse, do not encode.
        is FpType -> refuseFloatCell(type)
        else -> return null
      }
    return if (bits > 8 && bits % 8 == 0) bits / 8 else null
  }

  /** Whether [type] occupies more than one byte and is a whole number of them. */
  private fun wide(type: Type): Boolean = byteWidth(type) != null

  /**
   * Refuses a float in byte-addressed memory. See the class comment for why the IEEE round trip
   * cannot be trusted; the short version is that every NaN shares one bit pattern in SMT and the
   * theory does not say which, so the solver may choose the one that breaks the program.
   */
  private fun refuseFloatCell(type: FpType): Nothing =
    throw UnsupportedFrontendElementException(
      "A floating-point object ($type) in byte-addressed memory is not supported: splitting it" +
        " into byte cells requires the IEEE bit reinterpretation, which SMT-LIB leaves" +
        " underspecified for NaN (every NaN shares one encoding and the theory does not fix" +
        " which), so a program that inspects those bits can be given a spurious counterexample." +
        " Use --memory-model multi or flat for this input."
    )

  private fun XcfaLabel.bytify(): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.bytify() }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.bytify() }.toSet(), metadata)
      is StmtLabel ->
        when (stmt) {
          is MemoryAssignStmt<*, *, *> -> splitWrite(stmt)
          is AssignStmt<*> ->
            StmtLabel(
              AssignStmt.of(
                cast(stmt.varDecl, stmt.varDecl.type),
                cast(stmt.expr.expandReads(), stmt.varDecl.type),
              ),
              choiceType,
              metadata,
            )
          is AssumeStmt -> StmtLabel(AssumeStmt.of(stmt.cond.expandReads()), choiceType, metadata)
          else -> this
        }

      is InvokeLabel ->
        InvokeLabel(name, params.map { it.expandReads() }, metadata, tempLookup, isLibraryFunction)

      is StartLabel ->
        StartLabel(name, params.map { it.expandReads() }, pidVar, metadata, tempLookup)
      is ReturnLabel -> ReturnLabel(enclosedLabel.bytify())
      else -> this
    }

  /**
   * `(deref B O Bv_{8n}) := v` -> the `n` byte writes `(deref B O+j Bv8) := Extract(v, 8j, 8j+8)`.
   */
  private fun splitWrite(stmt: MemoryAssignStmt<*, *, *>): XcfaLabel {
    val deref = stmt.deref
    if (!wide(deref.type)) {
      return StmtLabel(
        rebuildMemoryAssign(deref.expandOps(), stmt.expr.expandReads()),
        metadata = EmptyMetaData,
      )
    }
    val base = deref.array.expandReads()
    val offset = deref.offset.expandReads()
    val rhs = stmt.expr.expandReads()
    val n = byteWidth(deref.type)!!
    val byteValues = ByteUnionSlice.toBytes(rhs, n)
    val writes =
      (0 until n).map { j ->
        val cell = byteCell(base, offset, j)
        StmtLabel(MemoryAssignStmt.create(cell, cast(byteValues[j], cell.type)))
      }
    return SequenceLabel(writes)
  }

  @Suppress("UNCHECKED_CAST")
  private fun rebuildMemoryAssign(
    deref: Dereference<*, *, *>,
    expr: Expr<*>,
  ): MemoryAssignStmt<*, *, *> = buildMemoryAssign(deref as Dereference<Type, Type, Type>, expr)

  private fun <P : Type, O : Type, D : Type> buildMemoryAssign(
    deref: Dereference<P, O, D>,
    expr: Expr<*>,
  ): MemoryAssignStmt<P, O, D> = MemoryAssignStmt.create(deref, cast(expr, deref.type))

  /** Replaces every wide dereference read inside this expression with its byte `Concat`. */
  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.expandReads(): Expr<T> =
    if (this is Dereference<*, *, *> && wide(type)) {
      val base = array.expandReads()
      val offset = offset.expandReads()
      val n = byteWidth(type)!!
      val cells = (0 until n).map { j -> byteCell(base, offset, j) as Expr<*> }
      cast(ByteUnionSlice.read(cells, (type as BvType).signed), type) as Expr<T>
    } else {
      withOps(ops.map { it.expandReads() }) as Expr<T>
    }

  /** Rebuilds a (byte) dereference with its base/offset sub-reads byte-expanded. */
  private fun Dereference<*, *, *>.expandOps(): Dereference<*, *, *> =
    Dereference.of(array.expandReads(), offset.expandReads(), type)

  /** The one-byte cell at byte `O + j` of base [base]. */
  private fun byteCell(base: Expr<*>, offset: Expr<*>, j: Int): Dereference<Type, Type, BvType> {
    val off: Expr<*> =
      if (j == 0) offset else Add(cast(offset, offset.type), literalOf(offset.type, j))
    return Dereference.of(cast(base, base.type), cast(off, base.type), BvType.of(8, false))
  }

  /**
   * A literal of value [value] at bitvector type [type] (offsets are bitvectors under this model).
   */
  private fun literalOf(type: Type, value: Int): Expr<*> {
    check(type is BvType) {
      "The bytes memory model requires bitvector arithmetic, found offset type $type"
    }
    return BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value.toLong()), type.size)
  }
}
