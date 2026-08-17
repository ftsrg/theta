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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * Copies memory, for the `mem*` functions that no one has defined.
 *
 * Nothing modelled them before: [UnresolvedInvokeToHavocPass] will not take a call whose arguments
 * are pointers, so `memcpy` reached the analysis as a call to a function that does not exist and
 * brought it down ("No such method memcpy"). The copy is spelled out instead, one element at a
 * time; nobody minds that it is long, only that it is right.
 *
 * The count is in **bytes**, but memory is modelled as `arrays[base][index]` over *typed* elements,
 * not bytes -- so the copy is done in the element type the pointer points at, `n / sizeof(element)`
 * of them. That is exact whenever the byte count is a whole number of elements, which is what
 * `memcpy(p, q, sizeof *p)` and `memcpy(buf, src, 100 * sizeof(char))` are.
 *
 * It also means the count has to be *known*. A symbolic one wants a loop, and a loop wants the
 * element size to divide a bound we cannot see -- so it is not attempted, and such a call is left
 * exactly as it was: it will still fail, loudly, which is the same as before and better than a copy
 * that quietly moves the wrong number of bytes.
 *
 * A pointer to a **struct** has no single element type, so it takes the other route: a whole-object
 * copy, driven by the object's cell layout rather than by any element width. That is the only
 * correct reading, because a cell is one *member*, whatever its C width -- a struct of four
 * `unsigned char` is four cells in four bytes. Restricted to objects whose every cell is a scalar:
 * a nested aggregate member's cell holds the *base id* of a separate object, and copying that cell
 * would make the two objects share storage instead of copying it.
 */
class MemoryFunctionsPass(val parseContext: ParseContext, val uniqueWarningLogger: Logger) :
  ProcedurePass {

  companion object {

    /** `dst`, `src`, `n` -- the copying pair. */
    private val COPY = setOf("memcpy", "memmove", "__builtin_memcpy", "__builtin_memmove")

    /** `dst`, `c`, `n` -- fills with a byte. */
    private val FILL = setOf("memset", "__builtin_memset")

    /** `mem`, `size` -- fills every byte with an independent nondeterministic value. */
    private val NONDET_FILL = setOf("__VERIFIER_nondet_memory")
  }

  private var nondetMemCounter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().map { it.name }.toSet()

    builder.getEdges().toList().forEach { edge ->
      val labels = edge.label.getFlatLabels()
      if (
        labels.none {
          it is InvokeLabel && it.name in COPY + FILL + NONDET_FILL && it.name !in defined
        }
      ) {
        return@forEach
      }
      val rewritten =
        labels.map { label ->
          if (label !is InvokeLabel || label.name in defined) label
          else if (label.name in COPY) copy(label) ?: label
          else if (label.name in FILL) fill(label) ?: label
          else if (label.name in NONDET_FILL) nondetFill(label, builder) ?: label else label
        }
      if (rewritten != labels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(rewritten)))
      }
    }
    return builder
  }

  /** `memcpy(dst, src, n)`: `dst[i] = src[i]` for every element the n bytes cover. */
  private fun copy(invoke: InvokeLabel): XcfaLabel? {
    // params are [returnValue, dst, src, n]
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val src = invoke.params[2]

    // A whole-object copy (`memcpy(p, q, sizeof *p)`, which is what these calls almost always are)
    // has to be driven by the object's *cell layout*, not by an element width: cells are one per
    // scalar member whatever its C width, so a struct of four `unsigned char` is four cells in four
    // bytes, not one.
    aggregateOf(dst)?.let { (pointee, cells, bytes) ->
      if (literalValue(invoke.params[3]) != bytes) return giveUp(invoke)
      val stmts =
        (0 until cells).map { i ->
          val cellType = cellTypeAt(pointee, i)
          MemoryAssignStmt.create(
            deref(dst, indexOf(i, dst), cellType),
            cast(deref(src, indexOf(i, src), cellType), cellType.smtType),
          )
        }
      return SequenceLabel(
        stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
      )
    }

    val element = elementOf(dst) ?: elementOf(src) ?: return giveUp(invoke)
    val count = elementCount(invoke.params[3], element) ?: return giveUp(invoke)

    val stmts =
      (0 until count).map { i ->
        val index = indexOf(i, dst)
        MemoryAssignStmt.create(
          deref(dst, index, element),
          cast(deref(src, indexOf(i, src), element), element.smtType),
        )
      }
    return SequenceLabel(
      stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
    )
  }

  /** `memset(dst, c, n)`: every element covered is set to `c`. */
  private fun fill(invoke: InvokeLabel): XcfaLabel? {
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val value = invoke.params[2]

    // `memset(p, 0, sizeof *p)` on an aggregate, by cells rather than by element width -- see the
    // matching branch in [copy]. Only the zero fill is claimed: a non-zero byte means something
    // different in every cell whose width is not one byte, and there is no honest cell value for
    // it.
    aggregateOf(dst)?.let { (pointee, cells, bytes) ->
      if (literalValue(value) != BigInteger.ZERO) return giveUp(invoke)
      if (literalValue(invoke.params[3]) != bytes) return giveUp(invoke)
      val stmts =
        (0 until cells).map { i ->
          val cellType = cellTypeAt(pointee, i)
          MemoryAssignStmt.create(
            deref(dst, indexOf(i, dst), cellType),
            cast(cellType.nullValue, cellType.smtType),
          )
        }
      return SequenceLabel(
        stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
      )
    }

    val element = elementOf(dst) ?: return giveUp(invoke)
    val count = elementCount(invoke.params[3], element) ?: return giveUp(invoke)

    // `memset` writes a *byte* into every byte. Setting whole elements to it is the same thing only
    // when the element is one byte wide -- or when the byte is zero, which makes every element zero
    // whatever its width. Any other case would be a different program, so it is not claimed.
    val zero = literalValue(value)?.equals(BigInteger.ZERO) == true
    if (!zero && element.width() != 8) return giveUp(invoke)

    // Convert to the *element's* type, not the argument's own. `memset` takes an `int` and stores
    // `(unsigned char)value` in each byte, so a literal like `memset(p, ' ', n)` arrives as a
    // 32-bit value that has to be narrowed to the one-byte element. Keeping it in the argument's
    // type left a Bv32 to be `cast(..., Bv8)`d below, which threw ClassCastException and failed the
    // whole frontend (`discover_list`).
    val filler = if (zero) element.nullValue as Expr<*> else element.castTo(value)
    val stmts =
      (0 until count).map { i ->
        MemoryAssignStmt.create(deref(dst, indexOf(i, dst), element), cast(filler, element.smtType))
      }
    return SequenceLabel(
      stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
    )
  }

  /**
   * `__VERIFIER_nondet_memory(mem, size)`: initialise `size` bytes at `mem` to arbitrary values --
   * one independent nondeterministic byte per cell, which is SV-COMP's own definition (`unsigned
   * char *p = mem; for i in [0, size): p[i] = __VERIFIER_nondet_uchar()`).
   *
   * Only spelled out under the **bytes** memory model, where it is sound: memory is one-byte cells
   * and every wider read is recombined from them, so a per-byte havoc is exactly visible to a later
   * read of any type overlapping the region. Under the 2-D model this would havoc a `uchar` array
   * that a sibling read of the same bytes at a wider type never sees -- a silent
   * under-approximation that could prove an unsafe program safe -- so it is left to fail loudly
   * instead. A symbolic or over-large size is likewise left unmodelled rather than havocing the
   * wrong number of bytes.
   */
  private fun nondetFill(invoke: InvokeLabel, builder: XcfaProcedureBuilder): XcfaLabel? {
    if (!parseContext.memoryModel.byteAddressed()) return null
    // The last two arguments are `mem` and `size`, whether or not a (void) return slot precedes
    // them.
    if (invoke.params.size < 2) return null
    val mem = invoke.params[invoke.params.size - 2]
    val size = literalValue(invoke.params[invoke.params.size - 1]) ?: return giveUp(invoke)
    if (size.signum() < 0 || size > BigInteger.valueOf(MAX_ELEMENTS)) return giveUp(invoke)

    val byteType = CUnsignedChar(null, parseContext)
    val stmts =
      (0 until size.toInt()).flatMap { i ->
        val fresh = Var("__nondet_mem_${nondetMemCounter++}", byteType.smtType)
        builder.addVar(fresh)
        val cell = deref(mem, indexOf(i, mem), byteType)
        listOf(
          StmtLabel(HavocStmt.of(fresh), metadata = invoke.metadata),
          StmtLabel(
            MemoryAssignStmt.create(cell, cast(fresh.ref, byteType.smtType)),
            metadata = invoke.metadata,
          ),
        )
      }
    return SequenceLabel(stmts)
  }

  /** `mem*` all return their destination; keep that, so `p = memcpy(p, q, n)` still works. */
  private fun returns(invoke: InvokeLabel, dst: Expr<*>): List<XcfaLabel> {
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return listOf()
    return listOf(
      AssignStmtLabel(
        cast(ret, ret.type),
        cast(CComplexType.getType(ret.ref, parseContext).castTo(dst), ret.type),
        metadata = invoke.metadata,
      )
    )
  }

  private fun giveUp(invoke: InvokeLabel): XcfaLabel? {
    uniqueWarningLogger.write(
      Logger.Level.INFO,
      "WARNING: ${invoke.name} with a byte count or element type that cannot be stated exactly" +
        " (a symbolic size, or a pointer to a compound); left unmodelled rather than copying the" +
        " wrong number of bytes.\n",
    )
    return null
  }

  /**
   * The type the argument points at, whatever it is.
   *
   * A struct-typed argument denotes the object itself, not a value: a struct's value in this model
   * *is* its base id, so `memcpy(&s, ...)` arrives typed `CStruct`, not `CPointer` to one -- and C
   * gives no other way for a struct to reach a `void *` parameter.
   */
  private fun pointeeOf(pointer: Expr<*>): CComplexType? =
    when (val type = CComplexType.getType(pointer, parseContext)) {
      is CStruct -> type
      is CArray -> type.embeddedType // CArray, CPointer and CStruct are all CIntegers here,
      is CPointer -> type.embeddedType // so the branches have to be spelled out in this order
      else -> null
    }

  /**
   * The type the pointer points at, for the *element-wise* copy -- scalars only, since a compound
   * has no single element type to copy in.
   *
   * ⚠️ `CStruct`, `CArray` and `CPointer` all extend `CInteger` in this type hierarchy, so the
   * `embedded is CInteger` test this used to end with was true for a struct as well. The pass's own
   * doc has always claimed a pointer to a struct is refused; in fact `memcpy(p, &d, 4)` on a
   * four-`unsigned char` struct silently resolved its element to the *struct*, whose `width()` is
   * 32, and copied `4 / 4 = 1` cell -- leaving three of the destination's four cells holding
   * whatever they held before, with no warning. A pointer element is a genuine one-cell scalar and
   * stays here; struct and array pointees go to [aggregateOf] instead.
   */
  private fun elementOf(pointer: Expr<*>): CComplexType? {
    val embedded = pointeeOf(pointer) ?: return null
    if (embedded is CStruct || embedded is CArray) return null
    return if (embedded is CInteger || embedded is CReal) embedded else null
  }

  /**
   * The pointee of [pointer] when it is an aggregate whose every cell is a scalar, along with that
   * cell count and its byte size -- null when the pointee is not an aggregate, or is one this
   * cannot state exactly.
   *
   * A nested aggregate member disqualifies the whole object: its parent cell holds the *base id* of
   * a separate object, so copying that cell would make the two objects share storage rather than
   * copy it. A union likewise, whose cells mean different things to different members.
   */
  private fun aggregateOf(pointer: Expr<*>): Triple<CComplexType, Int, BigInteger>? {
    val pointee = pointeeOf(pointer) ?: return null
    if (pointee !is CStruct && pointee !is CArray) return null
    val cells = flatCells(pointee) ?: return null
    val bits = ObjectLayout.of(pointee, parseContext.architecture).bitSize()
    if (bits <= 0 || bits % 8 != 0) return null
    return Triple(pointee, cells, BigInteger.valueOf((bits / 8).toLong()))
  }

  /** How many cells [type] occupies when all of them are scalars; null if any is not. */
  private fun flatCells(type: CComplexType): Int? =
    when {
      type is CArray -> {
        val dimension = ObjectLayout.constantDimension(type)
        val element = flatCells(type.embeddedType)
        if (dimension == null || element == null) null else dimension * element
      }

      type is CStruct ->
        if (type.isUnion || type.fields.any { it.get2() is CStruct || it.get2() is CArray }) null
        else type.unitCount

      else -> 1
    }

  /** The type of cell [index] of a flat aggregate. */
  private fun cellTypeAt(type: CComplexType, index: Int): CComplexType =
    when {
      type is CArray -> {
        val stride = flatCells(type.embeddedType) ?: 1
        cellTypeAt(type.embeddedType, if (stride > 0) index % stride else 0)
      }

      type is CStruct ->
        type.fields.firstOrNull { type.unitOffsetOf(it.get1()) == index }?.get2() ?: type

      else -> type
    }

  /** How many elements `n` bytes are, or null if that is not a whole, known number of them. */
  private fun elementCount(bytes: Expr<*>, element: CComplexType): Int? {
    val n = literalValue(bytes) ?: return null
    val size = BigInteger.valueOf((element.width() / 8).toLong())
    if (size.signum() == 0) return null
    val (count, remainder) = n.divideAndRemainder(size)
    if (remainder.signum() != 0) return null // a partial element: not ours to model
    if (count.signum() < 0 || count > BigInteger.valueOf(MAX_ELEMENTS)) return null
    return count.toInt()
  }

  /**
   * The value of a constant expression. `memcpy(p, q, 2 * sizeof(int))` reaches here as the
   * multiplication it was written as, not as `8`, so it has to be worked out rather than merely
   * looked at.
   */
  private fun literalValue(expr: Expr<*>): BigInteger? =
    when (val e = ExprUtils.simplify(expr)) {
      is IntLitExpr -> e.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(e)
      else -> null
    }

  /** The index of the i-th element, in the type the dereference's offset is built at. */
  private fun indexOf(i: Int, pointer: Expr<*>): Expr<*> =
    CComplexType.getUnsignedLong(parseContext).getValue("$i")

  @Suppress("UNCHECKED_CAST")
  private fun deref(pointer: Expr<*>, index: Expr<*>, element: CComplexType): Dereference<*, *, *> {
    val of = Dereference.of(pointer as Expr<Type>, index as Expr<Type>, element.smtType as Type)
    parseContext.metadata.create(of, "cType", element)
    return of
  }
}

/** Enough for any `sizeof` a benchmark copies; past it, a loop would be the honest model. */
private const val MAX_ELEMENTS = 4096L
