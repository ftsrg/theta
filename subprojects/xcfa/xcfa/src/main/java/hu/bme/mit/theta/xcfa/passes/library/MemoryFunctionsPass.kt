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
package hu.bme.mit.theta.xcfa.passes.library

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.property.MemsafetyPass
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
 * A symbolic or over-long count becomes a loop over `n / sizeof(element)` cells, with the partially
 * covered tail cell havoc'd. Anything the cell-per-value models cannot state exactly throws
 * [RequiresByteAddressedMemoryException], so the frontend rebuilds under the bytes model; there, a
 * call still not modelled is left in place and fails loudly as "No such method".
 *
 * The count and the fill value are read once, before the first write, as the writes may change what
 * those expressions read. The pass runs ahead of the memsafety guards. A straight-line region gets
 * one guard, on its first cell, as one guard per cell costs far more and checks nothing more.
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

    /** The copies whose regions may overlap: every source cell is read before any is written. */
    private val MOVE = setOf("memmove", "__builtin_memmove")

    /** `dst`, `c`, `n` -- fills with a byte. */
    private val FILL = setOf("memset", "__builtin_memset")

    /** `mem`, `size` -- fills every byte with an independent nondeterministic value. */
    private val NONDET_FILL = setOf("__VERIFIER_nondet_memory")
  }

  private var nondetMemCounter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().map { it.name }.toSet()

    // A symbolic byte count cannot be spelled out as straight-line assignments, so those calls are
    // lowered to a real loop instead -- which needs new locations, i.e. edge surgery rather than
    // the
    // label replacement below. Done first so the inline pass never sees them.
    builder.getEdges().toList().forEach { edge ->
      val labels = edge.label.getFlatLabels()
      val idx =
        labels.indexOfFirst {
          it is InvokeLabel &&
            it.name !in defined &&
            ((it.name in FILL && needsLoop(it)) || (it.name in COPY && needsCopyLoop(it)))
        }
      if (idx >= 0) {
        val invoke = labels[idx] as InvokeLabel
        if (invoke.name in FILL) fillLoop(builder, edge, labels, idx, invoke)
        else copyLoop(builder, edge, labels, idx, invoke)
      }
    }

    // A formatted write ends where its source string ends, which needs a loop as well.
    while (true) {
      val edge =
        builder.getEdges().firstOrNull { e ->
          e.label.getFlatLabels().any {
            it is InvokeLabel && it.name == FormatAccessPass.BOUNDED_WRITE
          }
        } ?: break
      val labels = edge.label.getFlatLabels()
      val idx =
        labels.indexOfFirst { it is InvokeLabel && it.name == FormatAccessPass.BOUNDED_WRITE }
      boundedWrite(builder, edge, labels, idx, labels[idx] as InvokeLabel)
    }

    // Same treatment for a nondet fill whose region is too large (or too unknown) to write out cell
    // by cell. A fresh snapshot, because the loop above may have replaced the edge this one is on.
    builder.getEdges().toList().forEach { edge ->
      val labels = edge.label.getFlatLabels()
      val idx =
        labels.indexOfFirst {
          it is InvokeLabel && it.name in NONDET_FILL && it.name !in defined && needsNondetLoop(it)
        }
      if (idx >= 0) nondetFillLoop(builder, edge, labels, idx, labels[idx] as InvokeLabel)
    }

    builder.getEdges().toList().forEach { edge ->
      val labels = edge.label.getFlatLabels()
      if (
        labels.none {
          it is InvokeLabel &&
            it.name in COPY + FILL + NONDET_FILL + FormatAccessPass.STRING_READ &&
            it.name !in defined
        }
      ) {
        return@forEach
      }
      val rewritten =
        labels.map { label ->
          if (label !is InvokeLabel || label.name in defined) label
          else if (label.name in COPY) copy(label, builder) ?: label
          else if (label.name in FILL) fill(label, builder) ?: label
          else if (label.name in NONDET_FILL) nondetFill(label, builder) ?: label
          else if (label.name == FormatAccessPass.STRING_READ) stringRead(label, builder) else label
        }
      if (rewritten != labels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(rewritten)))
      }
    }
    return builder
  }

  /** `memcpy(dst, src, n)`: `dst[i] = src[i]` for every element the n bytes cover. */
  private fun copy(invoke: InvokeLabel, builder: XcfaProcedureBuilder): XcfaLabel? {
    // params are [returnValue, dst, src, n]
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val src = invoke.params[2]
    if (parseContext.memoryModel.byteAddressed()) {
      val byte = CUnsignedChar(null, parseContext)
      val n = literalValue(invoke.params[3]) ?: return giveUp(invoke)
      if (n.signum() < 0 || n > BigInteger.valueOf(MAX_ELEMENTS)) return giveUp(invoke)
      return SequenceLabel(
        copyCells(invoke, builder, dst, src, List(n.toInt()) { byte }) + returns(invoke, dst)
      )
    }

    // A whole-object copy (`memcpy(p, q, sizeof *p)`, which is what these calls almost always are)
    // has to be driven by the object's *cell layout*, not by an element width: cells are one per
    // scalar member whatever its C width, so a struct of four `unsigned char` is four cells in four
    // bytes, not one.
    aggregateOf(dst)?.let { (pointee, cells, bytes) ->
      if (literalValue(invoke.params[3]) != bytes) return giveUp(invoke)
      val types = (0 until cells).map { cellTypeAt(pointee, it) }
      if (!laidOutAs(src, types)) return giveUp(invoke)
      return SequenceLabel(copyCells(invoke, builder, dst, src, types) + returns(invoke, dst))
    }

    val element = elementOf(dst) ?: elementOf(src) ?: return giveUp(invoke)
    val count = elementCount(invoke.params[3], element) ?: return giveUp(invoke)
    if (!laidOutAs(dst, List(count) { element }) || !laidOutAs(src, List(count) { element }))
      return giveUp(invoke)
    return SequenceLabel(
      copyCells(invoke, builder, dst, src, List(count) { element }) + returns(invoke, dst)
    )
  }

  /**
   * `dst[i] = src[i]` for each cell `i` of [types]. A `memmove` first reads every source cell into
   * a temporary: copied in place, `memmove(a + 1, a, 3)` overwrote `a[1]` before reading it.
   */
  private fun copyCells(
    invoke: InvokeLabel,
    builder: XcfaProcedureBuilder,
    dst: Expr<*>,
    src: Expr<*>,
    types: List<CComplexType>,
  ): List<XcfaLabel> {
    val reads =
      types.mapIndexed { i, type ->
        regionCell(deref(src, indexOf(i, src), type), i, types.size) as Expr<*>
      }
    val saves = mutableListOf<XcfaLabel>()
    val values =
      if (invoke.name !in MOVE) reads
      else
        reads.map { read ->
          val tmp = Var("__memmove_tmp_" + counter++, read.type)
          builder.addVar(tmp)
          saves.add(AssignStmtLabel(tmp, read, tmp.type, invoke.metadata))
          tmp.ref
        }
    return saves +
      types.mapIndexed { i, type ->
        StmtLabel(
          MemoryAssignStmt.create(
            regionCell(deref(dst, indexOf(i, dst), type), i, types.size),
            cast(values[i], type.smtType),
          ),
          metadata = invoke.metadata,
        )
      }
  }

  /** `memset(dst, c, n)`: every element covered is set to `c`. */
  private fun fill(invoke: InvokeLabel, builder: XcfaProcedureBuilder): XcfaLabel? {
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val value = invoke.params[2]
    if (parseContext.memoryModel.byteAddressed()) {
      val byte = CUnsignedChar(null, parseContext)
      val (c, save) = readOnce(builder, byte.castTo(value), byte, invoke)
      return byteWise(invoke, save) { i, cells ->
        MemoryAssignStmt.create(
          regionCell(deref(dst, indexOf(i, dst), byte), i, cells),
          cast(c, byte.smtType),
        )
      }
    }

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
            regionCell(deref(dst, indexOf(i, dst), cellType), i, cells),
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
    val (filler, save) =
      if (zero) element.nullValue as Expr<*> to listOf()
      else readOnce(builder, element.castTo(value), element, invoke)
    val stmts =
      (0 until count).map { i ->
        MemoryAssignStmt.create(
          regionCell(deref(dst, indexOf(i, dst), element), i, count),
          cast(filler, element.smtType),
        )
      }
    return SequenceLabel(
      save + stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
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
    // The last two arguments are `mem` and `size`, whether or not a (void) return slot precedes
    // them.
    if (invoke.params.size < 2) return null
    val mem = invoke.params[invoke.params.size - 2]
    val size = literalValue(invoke.params[invoke.params.size - 1]) ?: return giveUp(invoke)
    if (size.signum() < 0 || size > BigInteger.valueOf(MAX_ELEMENTS)) return giveUp(invoke)

    // Under the bytes model a cell IS a byte, so `size` cells are written. Under the typed-cell
    // models a cell is one element of the pointee type, so the byte count has to be divided by the
    // element width -- the same translation `fill` does.
    val byteAddressed = parseContext.memoryModel.byteAddressed()
    val cellType = if (byteAddressed) CUnsignedChar(null, parseContext) else elementOf(mem)
    if (cellType == null) return giveUp(invoke)
    val cells =
      if (byteAddressed) size.toInt()
      else (elementCount(invoke.params[invoke.params.size - 1], cellType) ?: return giveUp(invoke))

    val byteType = cellType
    val stmts =
      (0 until cells).flatMap { i ->
        val fresh = Var("__nondet_mem_${nondetMemCounter++}", byteType.smtType)
        builder.addVar(fresh)
        val cell = regionCell(deref(mem, indexOf(i, mem), byteType), i, cells)
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

  /**
   * The cell a nondet fill of [mem] writes, or null if this pass cannot name one.
   *
   * Under the bytes model a cell IS a byte, so any region can be filled a byte at a time. Under the
   * typed-cell models only a **scalar** pointee has a single cell type; a pointer to a compound is
   * refused for the soundness reason spelled out on [nondetFill].
   */
  private fun nondetCellType(mem: Expr<*>): CComplexType? =
    if (parseContext.memoryModel.byteAddressed()) CUnsignedChar(null, parseContext)
    else elementOf(mem)

  /**
   * A nondet fill that can only be modelled as a loop: the region is a whole number of cells this
   * pass can name, but writing them out one statement at a time is not on -- the size is symbolic,
   * or it is simply too big.
   */
  private fun needsNondetLoop(invoke: InvokeLabel): Boolean {
    if (invoke.params.size < 2) return false
    val cell = nondetCellType(invoke.params[invoke.params.size - 2]) ?: return false
    val width = cell.width()
    if (width <= 0 || width % 8 != 0) return false
    val n = literalValue(invoke.params[invoke.params.size - 1]) ?: return true
    if (n.signum() < 0) return false // not a size; giveUp says so more clearly
    return n > BigInteger.valueOf(MAX_ELEMENTS * (width / 8))
  }

  /**
   * `__VERIFIER_nondet_memory(mem, size)` over a region too large or too unknown to write out,
   * spelled as `for (i = 0; i < ceil(size / w); i++) { havoc v; mem[i] = v; }`.
   *
   * The straight-line lowering in [nondetFill] emits two statements per cell, so the 4096-cell cap
   * on it is not arbitrary -- and the intel-tdx firmware walks straight through it: its harness
   * calls this on whole objects, and `sizeof` is 36,864 for `tdcs_t`, 61,440 for `tdvps_t`, 81,920
   * for `tdx_module_global_t`. Written out, one call to the last of those is 163,840 statements. As
   * a loop it is four edges, and the havoc **inside the body** still gives each cell its own
   * unconstrained value, which is what makes this the same model rather than a weaker one.
   *
   * ⚠️ **The straddled tail cell is included**, hence `ceil` rather than a truncating divide: a
   * partially covered cell that kept its old value would hold one specific value the program never
   * wrote, which can hide a bug as easily as invent one. Unconstrained over-approximates it.
   *
   * ⚠️ Runs after [UnrollPass], so this reaches the analyses as a real loop and is never unrolled
   * -- deliberate, since unrolling 81,920 iterations is not a better answer but no answer.
   */
  private fun nondetFillLoop(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    labels: List<XcfaLabel>,
    idx: Int,
    invoke: InvokeLabel,
  ) {
    val mem = invoke.params[invoke.params.size - 2]
    val bytes = invoke.params[invoke.params.size - 1]
    val cell = nondetCellType(mem) ?: return
    val width = cell.width() / 8
    if (width <= 0) return

    val idxType = CComplexType.getUnsignedLong(parseContext)
    val i = Var("__nondet_mem_i_" + nondetMemCounter++, idxType.smtType)
    val v = Var("__nondet_mem_v_" + nondetMemCounter++, cell.smtType)
    builder.addVar(i)
    builder.addVar(v)

    val nCast = idxType.castTo(bytes)
    val w = idxType.getValue("$width")
    // ceil(n / w) == (n + w - 1) / w, over unsigned. `w - 1` is 0 for byte cells, where the region
    // is already a whole number of cells and this is just `n`.
    val count =
      Div(
        cast(
          Add(
            cast(nCast, idxType.smtType),
            cast(idxType.getValue("${width - 1}"), idxType.smtType),
          ),
          idxType.smtType,
        ),
        cast(w, idxType.smtType),
      )

    val head = XcfaLocation("__nondet_mem_head_" + counter, metadata = EmptyMetaData)
    val body = XcfaLocation("__nondet_mem_body_" + counter, metadata = EmptyMetaData)
    val exit = XcfaLocation("__nondet_mem_exit_" + counter++, metadata = EmptyMetaData)
    listOf(head, body, exit).forEach(builder::addLoc)

    val before = labels.subList(0, idx) + AssignStmtLabel(i, idxType.getValue("0"), i.type)
    val after = labels.subList(idx + 1, labels.size)

    builder.removeEdge(edge)
    builder.addEdge(XcfaEdge(edge.source, head, SequenceLabel(before), edge.metadata))
    builder.addEdge(
      XcfaEdge(
        head,
        body,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Lt(i.ref, count))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        head,
        exit,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(Lt(i.ref, count)))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        body,
        head,
        SequenceLabel(
          listOf(
            StmtLabel(HavocStmt.of(v), metadata = invoke.metadata),
            StmtLabel(
              MemoryAssignStmt.create(deref(mem, i.ref, cell), cast(v.ref, cell.smtType)),
              metadata = invoke.metadata,
            ),
            AssignStmtLabel(i, Add(i.ref, idxType.getValue("1")), i.type),
          )
        ),
        EmptyMetaData,
      )
    )
    builder.addEdge(XcfaEdge(exit, edge.target, SequenceLabel(after), EmptyMetaData))
  }

  private fun giveUp(invoke: InvokeLabel): XcfaLabel? {
    // Under the bytes model every object is its bytes, so the frontend retries there instead.
    if (!parseContext.memoryModel.byteAddressed()) {
      throw RequiresByteAddressedMemoryException(
        "${invoke.name} with a byte count or object layout the cell-per-value models cannot state" +
          " exactly"
      )
    }
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
   * copy it. A union likewise, whose cells mean different things to different members. Under
   * [CStruct.inlinesAggregates] only a union member is such a separate object.
   */
  private fun aggregateOf(pointer: Expr<*>): Triple<CComplexType, Int, BigInteger>? {
    val pointee = pointeeOf(pointer) ?: return null
    if (pointee !is CStruct && pointee !is CArray) return null
    val cells = flatCells(pointee) ?: return null
    val bits = ObjectLayout.of(pointee, parseContext.architecture).bitSize()
    if (bits <= 0 || bits % 8 != 0) return null
    return Triple(pointee, cells, BigInteger.valueOf((bits / 8).toLong()))
  }

  /**
   * Whether the object [pointer] points at starts with cells of exactly [types]. Both sides of a
   * copy are walked by one cell list, so a source of another layout (a different struct, a char
   * buffer behind a struct) would be read at the wrong cells. A `void *` says nothing and passes.
   */
  private fun laidOutAs(pointer: Expr<*>, types: List<CComplexType>): Boolean {
    val pointee = pointeeOf(pointer) ?: return true
    if (pointee is CVoid) return true
    val cells =
      if (pointee is CStruct || pointee is CArray) flatCells(pointee) ?: return false
      else Int.MAX_VALUE
    if (cells < types.size) return false
    return types.withIndex().all { (i, type) ->
      val actual = if (pointee is CStruct || pointee is CArray) cellTypeAt(pointee, i) else pointee
      actual.javaClass == type.javaClass && actual.width() == type.width()
    }
  }

  /** How many cells [type] occupies when all of them are scalars; null if any is not. */
  private fun flatCells(type: CComplexType): Int? =
    when {
      type is CArray -> {
        val dimension = ObjectLayout.constantDimension(type)
        val element = flatCells(type.embeddedType)
        if (dimension == null || element == null) null else dimension * element
      }

      type is CStruct && type.inlinesAggregates() ->
        if (type.fields.any { flatCells(it.get2()) == null }) null else type.unitCount

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

      type is CStruct && type.inlinesAggregates() -> {
        val field = type.fields.lastOrNull { type.unitOffsetOf(it.get1()) <= index } ?: return type
        cellTypeAt(field.get2(), index - type.unitOffsetOf(field.get1()))
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
  /**
   * Under the bytes model every byte is a cell of its own, so a copy or fill is exactly its `n`
   * byte moves, whatever the objects' types; [stmt] is the one for byte `i`.
   */
  private fun byteWise(
    invoke: InvokeLabel,
    save: List<XcfaLabel>,
    stmt: (Int, Int) -> MemoryAssignStmt<*, *, *>,
  ): XcfaLabel? {
    val n = literalValue(invoke.params[3]) ?: return giveUp(invoke)
    if (n.signum() < 0 || n > BigInteger.valueOf(MAX_ELEMENTS)) return giveUp(invoke)
    return SequenceLabel(
      save +
        (0 until n.toInt()).map { StmtLabel(stmt(it, n.toInt()), metadata = invoke.metadata) } +
        returns(invoke, invoke.params[1])
    )
  }

  /** Reads the first character of a string, which is what the guards check. */
  private fun stringRead(invoke: InvokeLabel, builder: XcfaProcedureBuilder): XcfaLabel {
    val byte = CUnsignedChar(null, parseContext)
    val string = invoke.params[0]
    val read = Var("__mem_string_read_" + counter++, byte.smtType)
    builder.addVar(read)
    return AssignStmtLabel(
      read,
      deref(string, indexOf(0, string), byte),
      read.type,
      invoke.metadata,
    )
  }

  /**
   * `sprintf(dst, "...%s...", src)`: walks `src` to its terminator, then reads the last byte the
   * call writes, as the guard of a contiguous region. `snprintf` writes at most `size` bytes.
   */
  private fun boundedWrite(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    labels: List<XcfaLabel>,
    idx: Int,
    invoke: InvokeLabel,
  ) {
    val source = invoke.params[2]
    val byte = CUnsignedChar(null, parseContext)
    val idxType = CComplexType.getUnsignedLong(parseContext)
    val i = Var("__mem_write_i_" + counter++, idxType.smtType)
    val read = Var("__mem_write_read_" + counter++, byte.smtType)
    builder.addVar(i)
    builder.addVar(read)
    val head = XcfaLocation("__mem_write_head_" + counter++, metadata = EmptyMetaData)
    builder.addLoc(head)
    val after = labels.subList(idx + 1, labels.size)
    val cell = deref(source, i.ref, byte)
    val zero = cast(byte.nullValue, byte.smtType)
    val size = invoke.params.getOrNull(3)
    val written = Add(cast(idxType.castTo(invoke.params[1]), idxType.smtType), i.ref)
    val last: Expr<*> =
      if (size == null) written
      else {
        val limit =
          Sub(
            cast(idxType.castTo(size), idxType.smtType),
            cast(idxType.getValue("1"), idxType.smtType),
          )
        Ite<Type>(Lt(written, limit), written, limit)
      }
    builder.removeEdge(edge)
    builder.addEdge(
      XcfaEdge(
        edge.source,
        head,
        SequenceLabel(labels.subList(0, idx) + AssignStmtLabel(i, idxType.getValue("0"), i.type)),
        edge.metadata,
      )
    )
    builder.addEdge(
      XcfaEdge(
        head,
        head,
        SequenceLabel(
          listOf(
            StmtLabel(AssumeStmt.of(Not(Eq(cell, zero)))),
            AssignStmtLabel(i, Add(i.ref, idxType.getValue("1")), i.type),
          )
        ),
        EmptyMetaData,
      )
    )
    val lastLabels =
      listOf(
        StmtLabel(AssumeStmt.of(Eq(deref(source, i.ref, byte), zero))),
        AssignStmtLabel(read, deref(invoke.params[0], last, byte), read.type, invoke.metadata),
      )
    builder.addEdge(XcfaEdge(head, edge.target, SequenceLabel(lastLabels + after), EmptyMetaData))
  }

  /** Marks cell [i] of a region of [cells] contiguous cells for one guard on the first cell. */
  private fun regionCell(cell: Dereference<*, *, *>, i: Int, cells: Int): Dereference<*, *, *> {
    if (i > 0) parseContext.metadata.create(cell, MemsafetyPass.GUARD_COVERED, true)
    else if (cells > 1) parseContext.metadata.create(cell, MemsafetyPass.GUARDED_SPAN, cells - 1)
    return cell
  }

  /** [value] as an expression the writes cannot change, and the labels that make it one. */
  private fun readOnce(
    builder: XcfaProcedureBuilder,
    value: Expr<*>,
    type: CComplexType,
    invoke: InvokeLabel,
  ): Pair<Expr<*>, List<XcfaLabel>> {
    if (literalValue(value) != null) return value to listOf()
    val saved = Var("__mem_arg_" + counter++, type.smtType)
    builder.addVar(saved)
    return saved.ref to listOf(AssignStmtLabel(saved, value, saved.type, invoke.metadata))
  }

  /** The cell a fill loop writes: a byte under the bytes model, else the pointee element. */
  private fun fillElement(pointer: Expr<*>): CComplexType? =
    if (parseContext.memoryModel.byteAddressed()) CUnsignedChar(null, parseContext)
    else elementOf(pointer)

  private fun indexOf(i: Int, pointer: Expr<*>): Expr<*> =
    CComplexType.getUnsignedLong(parseContext).getValue("$i")

  @Suppress("UNCHECKED_CAST")
  /** A fill this pass can only model as a loop: scalar element, but the byte count is symbolic. */
  private fun needsLoop(invoke: InvokeLabel): Boolean {
    if (invoke.params.size < 4) return false
    if (!parseContext.memoryModel.byteAddressed() && aggregateOf(invoke.params[1]) != null) {
      return false
    }
    val element = fillElement(invoke.params[1]) ?: return false
    if (!tooLargeOrSymbolic(invoke.params[3])) return false // the constant path handles it better
    if (element.width() <= 0 || element.width() % 8 != 0) return false
    val zero = literalValue(invoke.params[2])?.equals(BigInteger.ZERO) == true
    return zero || element.width() == 8
  }

  /**
   * `memset(dst, c, n)` with a **symbolic** `n`, spelled out as a loop over the elements the count
   * covers: `for (i = 0; i < n / sizeof *dst; i++) dst[i] = c`.
   *
   * The byte count only has to be translated into an element count -- `n / w` -- which is an
   * ordinary division on the count expression and needs nothing known at build time. A partial fill
   * of an array (`memset(arr, 0, k)` with `k` smaller than the object) falls out of the same bound.
   * A declined call is left in place and later surfaces as "No such method memset".
   *
   * ⚠️ **The partially covered tail element is havoc'd, not skipped.** When `n` is not a whole
   * number of elements the last one is only partly written, and leaving it holding its *old* value
   * would be a specific wrong value -- able to hide a bug as easily as to invent one. Unconstrained
   * is an over-approximation and safe, so the tail cell is havoc'd, guarded by `count * w != n` so
   * the common exact case keeps its precision.
   *
   * ⚠️ This runs after [UnrollPass], so the loop is never unrolled and reaches the analyses as a
   * real loop. That is deliberate: the alternative here is not a better answer but no answer at
   * all.
   */
  private fun fillLoop(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    labels: List<XcfaLabel>,
    idx: Int,
    invoke: InvokeLabel,
  ) {
    val dst = invoke.params[1]
    val value = invoke.params[2]
    val bytes = invoke.params[3]
    val element = fillElement(dst) ?: return
    val width = element.width() / 8
    if (width <= 0) return
    val zero = literalValue(value)?.equals(BigInteger.ZERO) == true
    val (filler, saveFiller) =
      if (zero) element.nullValue as Expr<*> to listOf()
      else readOnce(builder, element.castTo(value), element, invoke)

    val idxType = CComplexType.getUnsignedLong(parseContext)
    val i = Var("__memset_i_" + counter++, idxType.smtType)
    builder.addVar(i)
    val (nCast, saveCount) = readOnce(builder, idxType.castTo(bytes), idxType, invoke)
    val w = idxType.getValue("$width")
    val count = Div(cast(nCast, idxType.smtType), cast(w, idxType.smtType))

    val head = XcfaLocation("__memset_head_" + counter, metadata = EmptyMetaData)
    val body = XcfaLocation("__memset_body_" + counter, metadata = EmptyMetaData)
    val tail = XcfaLocation("__memset_tail_" + counter, metadata = EmptyMetaData)
    val exit = XcfaLocation("__memset_exit_" + counter, metadata = EmptyMetaData)
    listOf(head, body, tail, exit).forEach(builder::addLoc)

    val before =
      labels.subList(0, idx) +
        saveFiller +
        saveCount +
        AssignStmtLabel(i, idxType.getValue("0"), i.type)
    val after = returns(invoke, dst) + labels.subList(idx + 1, labels.size)

    builder.removeEdge(edge)
    builder.addEdge(XcfaEdge(edge.source, head, SequenceLabel(before), edge.metadata))
    // head: another element to write, or done
    builder.addEdge(
      XcfaEdge(
        head,
        body,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Lt(i.ref, count))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        head,
        tail,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(Lt(i.ref, count)))))),
        EmptyMetaData,
      )
    )
    // body: write this element and advance
    builder.addEdge(
      XcfaEdge(
        body,
        head,
        SequenceLabel(
          listOf(
            StmtLabel(
              MemoryAssignStmt.create(deref(dst, i.ref, element), cast(filler, element.smtType))
            ),
            AssignStmtLabel(i, Add(i.ref, idxType.getValue("1")), i.type),
          )
        ),
        EmptyMetaData,
      )
    )
    // tail: the count was not a whole number of elements -- the straddled cell is unconstrained
    val exact = Eq(Mul(count, cast(w, idxType.smtType)), nCast)
    val spill = Var("__memset_spill_" + counter++, element.smtType)
    builder.addVar(spill)
    builder.addEdge(
      XcfaEdge(tail, exit, SequenceLabel(listOf(StmtLabel(AssumeStmt.of(exact)))), EmptyMetaData)
    )
    builder.addEdge(
      XcfaEdge(
        tail,
        exit,
        SequenceLabel(
          listOf(
            StmtLabel(AssumeStmt.of(Not(exact))),
            StmtLabel(HavocStmt.of(spill)),
            StmtLabel(
              MemoryAssignStmt.create(deref(dst, count, element), cast(spill.ref, element.smtType))
            ),
          )
        ),
        EmptyMetaData,
      )
    )
    builder.addEdge(XcfaEdge(exit, edge.target, SequenceLabel(after), EmptyMetaData))
  }

  /**
   * True when the copy must run from the last cell down: the destination starts after the source in
   * the same object. Under the bytes model the addresses themselves are compared.
   */
  private fun overlapsAfter(dst: Expr<*>, src: Expr<*>, idxType: CComplexType): Expr<BoolType> {
    if (parseContext.memoryModel.byteAddressed()) {
      return Lt(
        cast(idxType.castTo(src), idxType.smtType),
        cast(idxType.castTo(dst), idxType.smtType),
      )
    }
    val zero = idxType.getValue("0")
    val (dstBase, dstOffset) = splitOffset(dst, zero)
    val (srcBase, srcOffset) = splitOffset(src, zero)
    val after =
      Lt(
        cast(idxType.castTo(srcOffset), idxType.smtType),
        cast(idxType.castTo(dstOffset), idxType.smtType),
      )
    return And(Eq(dstBase, srcBase), after)
  }

  /**
   * The cell a `memcpy` or `memmove` loop copies, when the byte count is symbolic or too long to
   * write out: a byte under the bytes model, else the scalar element both sides share.
   */
  private fun copyElement(invoke: InvokeLabel): CComplexType? {
    if (invoke.params.size < 4) return null
    if (!tooLargeOrSymbolic(invoke.params[3])) return null // the constant path handles it
    if (parseContext.memoryModel.byteAddressed()) return CUnsignedChar(null, parseContext)
    val dst = elementOf(invoke.params[1]) ?: return null
    val src = elementOf(invoke.params[2]) ?: return null
    if (dst.javaClass != src.javaClass || dst.width() != src.width()) return null
    return if (dst.width() > 0 && dst.width() % 8 == 0) dst else null
  }

  private fun needsCopyLoop(invoke: InvokeLabel): Boolean = copyElement(invoke) != null

  /** A byte count that cannot be written out as straight-line assignments. */
  private fun tooLargeOrSymbolic(bytes: Expr<*>): Boolean {
    val n = literalValue(bytes) ?: return true
    return n > BigInteger.valueOf(MAX_ELEMENTS)
  }

  /**
   * `memcpy(dst, src, n)` with a symbolic `n`: `for (i = 0; i < n / w; i++) dst[i] = src[i]`, with
   * the partially covered tail cell havoc'd exactly as in [fillLoop]. A `memmove` whose destination
   * lies after its source in the same object copies from the last cell down instead.
   */
  private fun copyLoop(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    labels: List<XcfaLabel>,
    idx: Int,
    invoke: InvokeLabel,
  ) {
    val dst = invoke.params[1]
    val src = invoke.params[2]
    val element = copyElement(invoke) ?: return
    val width = element.width() / 8

    val idxType = CComplexType.getUnsignedLong(parseContext)
    val i = Var("__memcpy_i_" + counter++, idxType.smtType)
    builder.addVar(i)
    val (nCast, saveCount) = readOnce(builder, idxType.castTo(invoke.params[3]), idxType, invoke)
    val w = idxType.getValue("$width")
    val count = Div(cast(nCast, idxType.smtType), cast(w, idxType.smtType))

    val head = XcfaLocation("__memcpy_head_" + counter, metadata = EmptyMetaData)
    val body = XcfaLocation("__memcpy_body_" + counter, metadata = EmptyMetaData)
    val tail = XcfaLocation("__memcpy_tail_" + counter, metadata = EmptyMetaData)
    val exit = XcfaLocation("__memcpy_exit_" + counter, metadata = EmptyMetaData)
    listOf(head, body, tail, exit).forEach(builder::addLoc)

    val before =
      labels.subList(0, idx) + saveCount + AssignStmtLabel(i, idxType.getValue("0"), i.type)
    val after = returns(invoke, dst) + labels.subList(idx + 1, labels.size)

    builder.removeEdge(edge)
    if (invoke.name in MOVE) {
      val choice = XcfaLocation("__memmove_choice_" + counter, metadata = EmptyMetaData)
      val downHead = XcfaLocation("__memmove_down_head_" + counter, metadata = EmptyMetaData)
      val downBody = XcfaLocation("__memmove_down_body_" + counter, metadata = EmptyMetaData)
      listOf(choice, downHead, downBody).forEach(builder::addLoc)
      val backward = overlapsAfter(dst, src, idxType)
      builder.addEdge(
        XcfaEdge(
          edge.source,
          choice,
          SequenceLabel(labels.subList(0, idx) + saveCount),
          edge.metadata,
        )
      )
      builder.addEdge(
        XcfaEdge(
          choice,
          head,
          SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(backward)))) + before.last()),
          EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          choice,
          downHead,
          SequenceLabel(
            listOf(StmtLabel(AssumeStmt.of(backward)), AssignStmtLabel(i, count, i.type))
          ),
          EmptyMetaData,
        )
      )
      val zero = cast(idxType.getValue("0"), idxType.smtType)
      builder.addEdge(
        XcfaEdge(
          downHead,
          downBody,
          SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Lt(zero, i.ref))))),
          EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          downHead,
          tail,
          SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(Lt(zero, i.ref)))))),
          EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          downBody,
          downHead,
          SequenceLabel(
            listOf(
              AssignStmtLabel(i, Sub(i.ref, idxType.getValue("1")), i.type),
              StmtLabel(
                MemoryAssignStmt.create(
                  deref(dst, i.ref, element),
                  cast(deref(src, i.ref, element), element.smtType),
                ),
                metadata = invoke.metadata,
              ),
            )
          ),
          EmptyMetaData,
        )
      )
    } else {
      builder.addEdge(XcfaEdge(edge.source, head, SequenceLabel(before), edge.metadata))
    }
    builder.addEdge(
      XcfaEdge(
        head,
        body,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Lt(i.ref, count))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        head,
        tail,
        SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(Lt(i.ref, count)))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        body,
        head,
        SequenceLabel(
          listOf(
            StmtLabel(
              MemoryAssignStmt.create(
                deref(dst, i.ref, element),
                cast(deref(src, i.ref, element), element.smtType),
              ),
              metadata = invoke.metadata,
            ),
            AssignStmtLabel(i, Add(i.ref, idxType.getValue("1")), i.type),
          )
        ),
        EmptyMetaData,
      )
    )
    val exact = Eq(Mul(count, cast(w, idxType.smtType)), nCast)
    val spill = Var("__memcpy_spill_" + counter++, element.smtType)
    builder.addVar(spill)
    builder.addEdge(
      XcfaEdge(tail, exit, SequenceLabel(listOf(StmtLabel(AssumeStmt.of(exact)))), EmptyMetaData)
    )
    builder.addEdge(
      XcfaEdge(
        tail,
        exit,
        SequenceLabel(
          listOf(
            StmtLabel(AssumeStmt.of(Not(exact))),
            StmtLabel(HavocStmt.of(spill)),
            StmtLabel(
              MemoryAssignStmt.create(deref(dst, count, element), cast(spill.ref, element.smtType))
            ),
          )
        ),
        EmptyMetaData,
      )
    )
    builder.addEdge(XcfaEdge(exit, edge.target, SequenceLabel(after), EmptyMetaData))
  }

  /**
   * `p + k` as the base `p` and index `k + index`, the way the frontend folds its own accesses:
   * under the cell models `arrays[p + k]` names no object, so `memcpy(a + 1, b, 3)` wrote to
   * nowhere and left `a` unchanged. The bytes model resolves addresses itself and takes the sum as
   * it is.
   */
  private fun splitOffset(pointer: Expr<*>, index: Expr<*>): Pair<Expr<*>, Expr<*>> {
    var stripped: Expr<*> = pointer
    while (stripped is PosExpr<*>) stripped = stripped.op
    if (parseContext.memoryModel.byteAddressed()) return pointer to index
    // The frontend reads a pointer-sum argument as an element's address: `a + 1` arrives as
    // `&a[1]`.
    if (stripped is Reference<*, *>) {
      val element = stripped.expr as? Dereference<*, *, *> ?: return pointer to index
      val pointee = pointeeOf(pointer)
      if (pointee is CStruct || pointee is CArray || pointee != pointeeOf(element.array)) {
        throw RequiresByteAddressedMemoryException(
          "A mem* call on an element address the cell-per-value models cannot fold: $pointer"
        )
      }
      val indexType = CComplexType.getUnsignedLong(parseContext)
      return element.array to Add(listOf(indexType.castTo(element.offset), indexType.castTo(index)))
    }
    if (stripped !is AddExpr<*>) return pointer to index
    val ops =
      stripped.ops.map {
        var op: Expr<*> = it
        while (op is PosExpr<*>) op = op.op
        op
      }
    val bases =
      ops.filter {
        CComplexType.getType(it, parseContext).let { t -> t is CPointer || t is CArray }
      }
    val pointee = pointeeOf(pointer)
    if (bases.size != 1 || pointee is CStruct || pointee is CArray) {
      throw RequiresByteAddressedMemoryException(
        "A mem* call on a pointer sum the cell-per-value models cannot fold: $pointer"
      )
    }
    val indexType = CComplexType.getUnsignedLong(parseContext)
    val offsets = (ops - bases.toSet()).map { indexType.castTo(it) } + indexType.castTo(index)
    return bases[0] to Add(offsets)
  }

  private var counter = 0

  private fun deref(pointer: Expr<*>, index: Expr<*>, element: CComplexType): Dereference<*, *, *> {
    val (base, offset) = splitOffset(pointer, index)
    val of = Dereference.of(base as Expr<Type>, offset as Expr<Type>, element.smtType as Type)
    parseContext.metadata.create(of, "cType", element)
    return of
  }
}

/** Enough for any `sizeof` a benchmark copies; past it, a loop would be the honest model. */
private const val MAX_ELEMENTS = 4096L
