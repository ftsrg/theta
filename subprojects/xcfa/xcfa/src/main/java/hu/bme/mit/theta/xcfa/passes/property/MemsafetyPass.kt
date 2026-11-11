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
package hu.bme.mit.theta.xcfa.passes.property

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.FlatAddressSpace
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.memory.PtrSizeToMemoryPass
import hu.bme.mit.theta.xcfa.passes.splitIf
import hu.bme.mit.theta.xcfa.utils.POINTER_BASE_CLASSES
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.ensureMallocVar
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.mallocVar
import java.util.Optional

/**
 * Adds assumptions to the XCFA if memory safety needs to be checked. Rules based on:
 * https://sv-comp.sosy-lab.org/2025/rules.php Summary:
 * - valid-free: All memory deallocations are valid (counterexample: invalid free). More precisely:
 *   There exists no finite execution of the program on which an invalid memory deallocation occurs.
 *     - inserted check: at every free, we check if pointer is valid (no NULLPTR, no double free).
 * - valid-deref: All pointer dereferences are valid (counterexample: invalid dereference). More
 *   precisely: There exists no finite execution of the program on which an invalid pointer
 *   dereference occurs.
 *     - inserted check: at every dereference, we check if pointer is valid (non-null, non-freed,
 *       in-size)
 * - valid-memtrack: All allocated memory is tracked, i.e., pointed to or deallocated
 *   (counterexample: memory leak). More precisely: There exists no finite execution of the program
 *   on which the program lost track of some previously allocated memory. (Comparison to Valgrind:
 *   This property is violated if Valgrind reports 'definitely lost'.)
 *     - inserted check: we keep track of variables.
 */
class MemsafetyPass(private val property: XcfaProperty, private val parseContext: ParseContext) :
  ProcedurePass {

  companion object {
    /** On a dereference: how many further address units its one guard covers. */
    const val GUARDED_SPAN = "memsafetyGuardedSpan"

    /** On a dereference: it needs no guard, as a [GUARDED_SPAN] of the same region covers it. */
    const val GUARD_COVERED = "memsafetyGuardCovered"

    private const val STATIC_SIZES_KEY = "staticObjectSizes"
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!parseContext.isCheckMemsafety) return blockNullDerefs(builder)

    breakUpErrors(builder)

    // The deref check bounds addresses by the allocation counter, so it must exist even when the
    // program allocates nothing at runtime; seeding it also registers the static slots.
    if (parseContext.memoryModel.flatAddressing()) {
      builder.parent.ensureMallocVar(parseContext, pointerType)
    }

    annotateFree(builder)

    annotateDeref(builder)

    if (builder in builder.parent.getInitProcedures().map { it.first }) {
      annotateLost(builder)
    }

    property.transformSpecification(ErrorDetection.ERROR_LOCATION)
    return builder
  }

  private val pointerType = CPointer(null, null, parseContext)
  val fitsall = Fitsall(null, parseContext)

  private fun breakUpErrors(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val finalLoc =
      builder.finalLoc.orElseGet { builder.createFinalLoc().let { builder.finalLoc.get() } }

    LinkedHashSet(errorLoc.incomingEdges).forEach {
      builder.removeEdge(it)
      builder.addEdge(it.withTarget(finalLoc))
    }
  }

  private fun annotateFree(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }

    val invalidFree = XcfaLocation("__THETA_bad_free", metadata = EmptyMetaData)
    builder.addLoc(invalidFree)
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::free)
      if (
        edges.size > 1 || (edges.size == 1 && free((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (free((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            val argument = invokeLabel.params[1]
            val sizeVar = builder.parent.getPtrSizeVar()
            val derefAssume =
              And(
                // "If ptr is a null pointer, no action occurs" -- C17 7.22.3.3. `free(NULL)` is not
                // merely tolerated, it is the idiom every cleanup path is written around, and it
                // was
                // being reported as an invalid free: a null pointer has no recorded size, so the
                // bound below took it for one that was never allocated.
                Neq(argument, pointerType.nullValue),
                Or(
                  Lt(argument, pointerType.nullValue), // uninit ptr
                  // Already freed, or never allocated: both leave 0, while a live block, even an
                  // empty one, holds its size + 1 (see allocate). The bound is Fitsall-typed like
                  // the array -- a pointer-typed zero is narrower under bitvector arithmetic.
                  Leq(ArrayReadExpr.create<Type, Type>(sizeVar.ref, argument), fitsall.nullValue),
                  // Only the heap may be freed; the size check above cannot catch the rest, since
                  // an alloca'd block records a real size too.
                  notHeap(builder, argument),
                ),
              )

            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(
                  listOf(
                    StmtLabel(Assume(Not(derefAssume)), metadata = it.label.labels[0].metadata),
                    builder.parent.deallocate(parseContext, argument),
                  )
                ),
                it.metadata,
              )
            )
            builder.addEdge(
              XcfaEdge(
                it.source,
                invalidFree,
                SequenceLabel(
                  listOf(StmtLabel(Assume(derefAssume), metadata = it.label.labels[0].metadata))
                ),
                it.metadata,
              )
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    // A single shared exit edge: one per check would pile up parallel label-less edges on
    // `invalidFree`, which the OC backend rejects as a branching location without assumes.
    if (invalidFree.incomingEdges.isNotEmpty()) {
      builder.addEdge(
        XcfaEdge(invalidFree, errorLoc, SequenceLabel(listOf(NopLabel)), EmptyMetaData)
      )
    }
  }

  private fun annotateDeref(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val badDeref = XcfaLocation("__THETA_bad_deref", metadata = EmptyMetaData)
    builder.addLoc(badDeref)
    val branchEntries = separateDerefBranches(builder)
    for (edge in ArrayList(builder.getEdges())) {
      if (edge in branchEntries.values) continue
      val edges = edge.splitIf(this::deref)
      if (
        edges.size > 1 || (edges.size == 1 && deref((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (
            deref((it.label as SequenceLabel).labels[0]) &&
              !builder.ptrSizeAssign(it.label.labels[0])
          ) {
            // if dereference is in a short-circuiting path, add prior assumptions as well.
            val witnesses = mutableListOf<XcfaLabel>()
            val derefAssume =
              Or(
                it.label.labels[0].derefsWithShortCircuitCond.map { (deref, shortCircuitConds) ->
                  val sizeVar = builder.parent.getPtrSizeVar()
                  if (parseContext.memoryModel.flatAddressing()) {
                    val (witnessLabels, bad) = flatDerefCheck(builder, deref)
                    witnesses.addAll(witnessLabels)
                    return@map And(And(shortCircuitConds), bad)
                  }
                  val sizeKey = deref.array
                  val indexInObject = deref.offset.toFitsall()
                  // Past the last unit accessed, as the array holds size + 1 (see allocate).
                  val end = Add(indexInObject, fitsall.getValue("${lastByte(deref) + 1}"))
                  And(
                    And(shortCircuitConds),
                    Or(
                      Leq(sizeKey, pointerType.nullValue), // uninit ptr
                      // Sizes are Fitsall-typed, offsets are pointer-typed: the offset has to be
                      // widened to compare against a size (they are the same unbounded Int under
                      // integer arithmetic, but different bitvector widths otherwise).
                      Leq(
                        ArrayReadExpr.create<Type, Type>(sizeVar.ref, sizeKey),
                        end,
                      ), // freed/not big enough ptr
                      Lt(indexInObject, fitsall.nullValue), // negative index
                    ),
                  )
                }
              )
            // The witnesses come before the branch: OC needs the two edges to start with assumes.
            val entry = branchEntries[it.source]
            val check =
              when {
                witnesses.isEmpty() -> it.source
                entry != null -> {
                  builder.removeEdge(entry)
                  val labels = (entry.label as SequenceLabel).labels + witnesses
                  branchEntries[it.source] =
                    entry.withLabel(SequenceLabel(labels)).also(builder::addEdge)
                  it.source
                }
                else ->
                  XcfaLocation("__THETA_deref_check_${witnessCount}", metadata = EmptyMetaData)
                    .also { check ->
                      builder.addLoc(check)
                      builder.addEdge(
                        XcfaEdge(it.source, check, SequenceLabel(witnesses), it.metadata)
                      )
                    }
              }
            builder.addEdge(
              XcfaEdge(
                check,
                it.target,
                SequenceLabel(
                  listOf(
                    StmtLabel(Assume(Not(derefAssume)), metadata = it.label.labels[0].metadata),
                    it.label,
                  )
                ),
                it.metadata,
              )
            )
            builder.addEdge(
              XcfaEdge(
                check,
                badDeref,
                SequenceLabel(
                  listOf(StmtLabel(Assume(derefAssume), metadata = it.label.labels[0].metadata))
                ), // deref(x a), x <= 0 || a >= sizeof(x)
                it.metadata,
              )
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    // A single shared exit edge: one per check would pile up parallel label-less edges on
    // `badDeref`, which the OC backend rejects as a branching location without assumes.
    if (badDeref.incomingEdges.isNotEmpty()) {
      builder.addEdge(XcfaEdge(badDeref, errorLoc, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
    }
  }

  /**
   * Gives each location branching on a dereference, as `if (*p)` does, a separate entry edge, where
   * the witnesses of its branches can go under flat addressing. Returns the entry edges by
   * location.
   */
  private fun separateDerefBranches(
    builder: XcfaProcedureBuilder
  ): MutableMap<XcfaLocation, XcfaEdge> {
    val entries = mutableMapOf<XcfaLocation, XcfaEdge>()
    if (!parseContext.memoryModel.flatAddressing()) return entries
    builder.getLocs().toList().forEach { loc ->
      val branches = loc.outgoingEdges.toList()
      if (
        branches.size < 2 ||
          branches.none { it.getFlatLabels().firstOrNull()?.let(::deref) == true }
      )
        return@forEach
      val branching = XcfaLocation("${loc.name}_deref_branch", metadata = EmptyMetaData)
      builder.addLoc(branching)
      branches.forEach {
        builder.removeEdge(it)
        builder.addEdge(XcfaEdge(branching, it.target, it.label, it.metadata))
      }
      entries[branching] =
        XcfaEdge(loc, branching, SequenceLabel(listOf()), EmptyMetaData).also(builder::addEdge)
    }
    return entries
  }

  /**
   * Without the memory-safety properties, a dereference of NULL crashes the program, so it ends the
   * path instead of reading or writing memory at address zero (e.g., after a failed `malloc`).
   * Under flat addressing the base already includes member offsets, hence the whole null page.
   */
  private fun blockNullDerefs(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (edge in ArrayList(builder.getEdges())) {
      val guarded = guardNullDerefs(edge.label)
      if (guarded == listOf(edge.label) || guarded == (edge.label as? SequenceLabel)?.labels)
        continue
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(guarded, edge.label.metadata)))
    }
    return builder
  }

  /** [label], each dereferencing step preceded by an assumption that its base is not NULL. */
  private fun guardNullDerefs(label: XcfaLabel): List<XcfaLabel> =
    when (label) {
      is SequenceLabel -> label.labels.flatMap(::guardNullDerefs)
      is NondetLabel -> {
        val branches =
          label.labels.map { branch ->
            val guarded = guardNullDerefs(branch)
            if (guarded == listOf(branch)) branch else SequenceLabel(guarded)
          }
        if (branches.toSet() == label.labels) listOf(label)
        else listOf(NondetLabel(branches.toSet(), label.metadata))
      }
      else -> {
        // Any other literal base is a static object.
        val derefs =
          label.derefsWithShortCircuitCond.filter {
            it.first.array !is LitExpr<*> || it.first.array == pointerType.nullValue
          }
        if (derefs.isEmpty()) listOf(label)
        else {
          val isNull = Or(derefs.map { (deref, conds) -> And(And(conds), isNull(deref)) })
          listOf(StmtLabel(Assume(Not(isNull)), metadata = label.metadata), label)
        }
      }
    }

  private fun isNull(deref: Dereference<*, *, *>): Expr<BoolType> {
    val base = pointerType.castTo(deref.array)
    if (!parseContext.memoryModel.flatAddressing()) return Eq(base, pointerType.nullValue)
    val ptr = pointerType.smtType
    val addr = Add(cast(base, ptr), cast(pointerType.castTo(deref.offset), ptr))
    return And(
      Geq(addr, pointerType.nullValue),
      Lt(addr, pointerType.getValue(FlatAddressSpace.FIRST.toString())),
    )
  }

  /**
   * The offset of the last address unit [deref]'s guard covers from its first: its [GUARDED_SPAN],
   * and under the bytes model the width of the value it accesses (its recorded C type is its
   * address).
   */
  private fun lastByte(deref: Dereference<*, *, *>): Int {
    val span =
      parseContext.metadata.getMetadataValue(deref, GUARDED_SPAN).map { it as Int }.orElse(0)
    if (!parseContext.memoryModel.byteAddressed()) return span
    val bits = (deref.type as? BvType)?.size ?: return span
    return span + maxOf((bits + 7) / 8 - 1, 0)
  }

  private fun needsGuard(deref: Dereference<*, *, *>): Boolean =
    !parseContext.metadata.getMetadataValue(deref, GUARD_COVERED).isPresent

  /**
   * The valid-deref check of [deref] under flat addressing, which has no object base to read off
   * the address. A fresh witness `w` is assumed to be the start of the slot containing the address
   * `a` -- exactly one does when `a` is in `[FIRST, __malloc)`, as the slots tile that range -- and
   * the access is bad when `a` is outside the range or past the live size of `w`'s object. When the
   * dereference's base is itself a slot start holding `a`, `w` is that base, and the check reads it
   * directly.
   *
   * Returns the labels introducing the witness, and the bad condition.
   */
  private fun flatDerefCheck(
    builder: XcfaProcedureBuilder,
    deref: Dereference<*, *, *>,
  ): Pair<List<XcfaLabel>, Expr<BoolType>> {
    val ptr = pointerType.smtType
    val sizeVar = builder.parent.getPtrSizeVar()
    staticSizes(builder.parent)?.let { sizes ->
      val address =
        Add(cast(pointerType.castTo(deref.array), ptr), cast(pointerType.castTo(deref.offset), ptr))
      val valid = sizes.map { (start, size) -> inObject(address, start, size) }
      return Pair(emptyList(), Not(Or(valid)))
    }
    val extentVar = builder.parent.getObjExtentVar()!!
    val counter = builder.parent.mallocVar(parseContext)
    val witness = Var("__theta_slot_${witnessCount++}", ptr)
    builder.addVar(witness)
    val addr =
      Add(cast(pointerType.castTo(deref.array), ptr), cast(pointerType.castTo(deref.offset), ptr))
    val inRange =
      And(
        Geq(addr, pointerType.getValue(FlatAddressSpace.FIRST.toString())),
        Lt(addr, cast(counter.ref, ptr)),
      )
    val index = Sub(addr, witness.ref).toFitsall()
    val extent = ArrayReadExpr.create<Type, Type>(extentVar.ref, witness.ref)
    val inSlot =
      And(listOf(Leq(witness.ref, addr), Lt(index, extent), Gt(extent, fitsall.nullValue)))
    val size = ArrayReadExpr.create<Type, Type>(sizeVar.ref, witness.ref)
    // Fast path: the base is a slot start and the offset lies in its slot, so the witness can only
    // be the base. Deciding that without the witness is what keeps the common access cheap.
    val base = cast(pointerType.castTo(deref.array), ptr)
    val offset = cast(pointerType.castTo(deref.offset), ptr).toFitsall()
    val baseExtent = ArrayReadExpr.create<Type, Type>(extentVar.ref, base)
    val direct =
      And(
        listOf(
          Gt(baseExtent, fitsall.nullValue),
          Geq(offset, fitsall.nullValue),
          Lt(offset, baseExtent),
        )
      )
    val baseSize = ArrayReadExpr.create<Type, Type>(sizeVar.ref, base)
    // Under bytes the access spans its value's bytes, all of which must be in the object. Past the
    // last of them, as the array holds size + 1 (see allocate).
    val end = fitsall.getValue("${lastByte(deref) + 1}")
    @Suppress("UNCHECKED_CAST")
    val bad =
      Ite<BoolType>(
        direct,
        Leq(baseSize, Add(offset, end)),
        Or(Not(inRange), Leq(size, Add(index, end))),
      )
        as Expr<BoolType>
    return Pair(
      listOf(StmtLabel(HavocStmt.of(witness)), StmtLabel(Assume(Or(Not(inRange), inSlot)))),
      bad,
    )
  }

  /**
   * The start and size of each object when these are constants: all set on the entry path and
   * nothing released. A check is then a condition over the address alone, with no witness or ghost
   * array.
   */
  @Suppress("UNCHECKED_CAST")
  private fun staticSizes(xcfa: XcfaBuilder): Map<LitExpr<*>, LitExpr<*>>? =
    (xcfa.metaData.getOrPut(STATIC_SIZES_KEY) { Optional.ofNullable(collectStaticSizes(xcfa)) }
        as Optional<Map<LitExpr<*>, LitExpr<*>>>)
      .orElse(null)

  private fun collectStaticSizes(xcfa: XcfaBuilder): Map<LitExpr<*>, LitExpr<*>>? {
    val ghosts = listOfNotNull(xcfa.getPtrSizeVar(), xcfa.getObjExtentVar(), xcfa.getObjHeapVar())
    val pass = PtrSizeToMemoryPass(parseContext)
    val labels = xcfa.getProcedures().flatMap { p -> p.getEdges().map { it to p } }
    if (
      !PtrSizeToMemoryPass.enabled ||
        FunctionIds.hasIndirectCall() ||
        labels.any { (edge, _) -> edge.getFlatLabels().any(::free) }
    )
      return null
    val (init, _) = xcfa.getInitProcedures().singleOrNull() ?: return null
    val sizes = mutableMapOf<LitExpr<*>, LitExpr<*>>()
    val entry = mutableSetOf<XcfaLabel>()
    var loc = init.initLoc
    val seen = mutableSetOf(loc)
    while (loc.outgoingEdges.size == 1) {
      val edge = loc.outgoingEdges.first()
      edge.getFlatLabels().forEach { label ->
        val assign = (label as? StmtLabel)?.stmt as? AssignStmt<*>
        if (assign?.varDecl in ghosts) {
          val cells = assign!!.expr.let { with(pass) { it.constantCells(assign.varDecl) } }
          if (cells != null) {
            entry.add(label)
            if (assign.varDecl == xcfa.getPtrSizeVar()) sizes.putAll(cells)
          }
        }
      }
      loc = edge.target
      if (!seen.add(loc)) break
    }
    val onlyOnEntry =
      labels.none { (edge, _) -> edge.getFlatLabels().any { it !in entry && it.writesAny(ghosts) } }
    return sizes.takeIf { onlyOnEntry }
  }

  private fun XcfaLabel.writesAny(ghosts: List<VarDecl<*>>): Boolean =
    collectVarsWithAccessType().any { (variable, access) -> variable in ghosts && access.isWritten }

  /** [size] as the array holds it, size + 1 (see allocate). */
  private fun inObject(address: Expr<*>, start: LitExpr<*>, size: LitExpr<*>): Expr<BoolType> {
    val index = Sub(address, cast(start, address.type)).toFitsall()
    return And(Geq(address, cast(start, address.type)), Lt(Add(index, fitsall.unitValue), size))
  }

  private var witnessCount = 0

  /** Whether [ptr] is not the start of a heap block, i.e. may not be freed. */
  private fun notHeap(builder: XcfaProcedureBuilder, ptr: Expr<*>): Expr<BoolType> {
    val heapVar = builder.parent.getObjHeapVar()
    return if (heapVar != null)
      Eq(ArrayReadExpr.create<Type, Type>(heapVar.ref, ptr), fitsall.nullValue)
    else
    // The `3k+0` class (see POINTER_BASE_CLASSES). `Rem`, not `Mod`: pointer types are unsigned
    // bitvectors and Theta's `Mod` is signed-only.
    Neq(Rem(ptr, pointerType.getValue("$POINTER_BASE_CLASSES")), pointerType.nullValue)
  }

  private fun Expr<*>.toFitsall(): Expr<*> =
    if (fitsall.smtType is IntType) this else fitsall.castTo(this)

  fun annotateLost(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val finalLoc =
      builder.finalLoc.orElseGet { builder.createFinalLoc().let { builder.finalLoc.get() } }
    val lostLoc = XcfaLocation("__THETA_lost", metadata = EmptyMetaData)
    builder.addLoc(lostLoc)

    val sizeVar = builder.parent.getPtrSizeVar()
    val anyBase =
      builder.parent.getVars().find { it.wrappedVar.name == "__ptr" }?.wrappedVar
        ?: XcfaGlobalVar(Var("__ptr", sizeVar.type.indexType), pointerType.nullValue)
          .also { builder.parent.addVar(it) }
          .wrappedVar
    // Ranges over heap block starts: the 3k+0 class under multi, the heap ghost under flat.
    // Multiplying
    // by 3 would not stay in the class: on bitvectors it wraps onto every address.
    val mallocBase = anyBase.ref
    // A live block holds size + 1 (see allocate); a lost empty block is not reported.
    val liveSize = Gt(ArrayReadExpr.create<Type, Type>(sizeVar.ref, mallocBase), fitsall.unitValue)
    val stillAllocated = And(liveSize, Not(notHeap(builder, mallocBase)))

    // valid-memtrack is "pointed to OR deallocated" -- Valgrind's *definitely* lost -- so a block a
    // live pointer still names is tracked, freed or not. Checking only whether everything was freed
    // reported a leak for the ordinary `char *v; v = malloc(1);` shape, where the global keeps
    // pointing at the block for the whole run and nothing is ever lost (sv-benchmarks `singleton`
    // and friends expect `true` there). Locals are gone by the final location, so the pointers that
    // can still name a block are the global ones; a block reachable only *through* another heap
    // block is not covered, which keeps this on the safe side -- it can only report a leak that is
    // not one, never miss one.
    // ...but only for valid-memtrack. `valid-memcleanup` is the stricter property: *all* memory
    // must be released before the program exits, and whether something still points at a block is
    // beside the point -- `CWE401_Memory_Leak`, a global holding a never-freed malloc, is a
    // violation of memcleanup and not of memtrack. Applying the exemption to both turned 32 of
    // those from correct into missed leaks.
    val trackedIfPointedTo = property.inputProperty != ErrorDetection.MEMCLEANUP
    val globalPointers =
      if (!trackedIfPointedTo) emptyList()
      else
        builder.parent
          .getVars()
          .map { it.wrappedVar }
          .filter { it != anyBase && it != sizeVar }
          // A ghost (`__malloc`, the slot arrays) may have no C type at all; it is not a pointer.
          .filter {
            runCatching { CComplexType.getType(it.ref, parseContext) }.getOrNull() is CPointer
          }
    val pointedTo = globalPointers.map { Eq(cast(it.ref, mallocBase.type), mallocBase) }
    val remained =
      if (pointedTo.isEmpty()) stillAllocated else And(stillAllocated, Not(Or(pointedTo)))

    val preFinalHavoc = XcfaLocation("_pre_final_havoc", metadata = EmptyMetaData)
    val preFinal = XcfaLocation("_pre_final", metadata = EmptyMetaData)
    builder.addLoc(preFinalHavoc)
    for (incomingEdge in LinkedHashSet(finalLoc.incomingEdges)) {
      builder.removeEdge(incomingEdge)
      builder.addEdge(incomingEdge.withTarget(preFinalHavoc))
    }
    builder.addEdge(
      XcfaEdge(
        preFinalHavoc,
        preFinal,
        SequenceLabel(listOf(StmtLabel(HavocStmt.of(anyBase)))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(
        preFinal,
        finalLoc,
        SequenceLabel(listOf(StmtLabel(Assume(Not(remained))))),
        EmptyMetaData,
      )
    )
    builder.addEdge(
      XcfaEdge(preFinal, lostLoc, SequenceLabel(listOf(StmtLabel(Assume(remained)))), EmptyMetaData)
    )
    builder.addEdge(XcfaEdge(lostLoc, errorLoc, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
  }

  private fun free(it: XcfaLabel): Boolean {
    return it is InvokeLabel && it.name == "free"
  }

  private fun deref(it: XcfaLabel): Boolean {
    return it.derefsWithShortCircuitCond.isNotEmpty()
  }

  private fun XcfaProcedureBuilder.ptrSizeAssign(it: XcfaLabel): Boolean {
    return it is StmtLabel && it.stmt is AssignStmt<*> && it.stmt.varDecl == parent.getPtrSizeVar()
  }

  private val XcfaLabel.derefsWithShortCircuitCond:
    List<Pair<Dereference<*, *, *>, List<Expr<BoolType>>>>
    get() =
      when (this) {
        is StmtLabel -> stmt.derefsWithShortCircuitCond
        is InvokeLabel -> params.flatMap { it.derefsWithShortCircuitCond }
        is NondetLabel -> labels.flatMap { it.derefsWithShortCircuitCond }
        is SequenceLabel -> labels.flatMap { it.derefsWithShortCircuitCond }
        is StartLabel -> params.flatMap { it.derefsWithShortCircuitCond }
        is FenceLabel -> lock.derefsWithShortCircuitCond
        else -> emptyList()
      }

  val Stmt.derefsWithShortCircuitCond: List<Pair<Dereference<*, *, *>, List<Expr<BoolType>>>>
    get() =
      when (this) {
        is AssumeStmt -> cond.derefsWithShortCircuitCond
        is AssignStmt<*> -> expr.derefsWithShortCircuitCond
        is MemoryAssignStmt<*, *, *> ->
          expr.derefsWithShortCircuitCond +
            (if (needsGuard(deref)) listOf(deref to listOf()) else listOf())
        else -> emptyList()
      }

  private val Expr<*>.derefsWithShortCircuitCond:
    List<Pair<Dereference<*, *, *>, List<Expr<BoolType>>>>
    get() =
      when (this) {
        is AndExpr -> {
          val conditions = mutableListOf<Expr<BoolType>>()
          ops.flatMap { op ->
            val derefs =
              op.derefsWithShortCircuitCond.map { (deref, conds) -> deref to (conditions + conds) }
            conditions.add(op)
            derefs
          }
        }

        is OrExpr -> {
          val conditions = mutableListOf<Expr<BoolType>>()
          ops.flatMap { op ->
            val derefs =
              op.derefsWithShortCircuitCond.map { (deref, conds) -> deref to (conditions + conds) }
            conditions.add(Not(op))
            derefs
          }
        }

        is IteExpr<*> ->
          cond.derefsWithShortCircuitCond +
            then.derefsWithShortCircuitCond.map { (deref, conds) ->
              deref to (listOf(cond) + conds)
            } +
            `else`.derefsWithShortCircuitCond.map { (deref, conds) ->
              deref to (listOf(Not(cond)) + conds)
            }

        is Dereference<*, *, *> -> {
          ops.flatMap { it.derefsWithShortCircuitCond } +
            (if (needsGuard(this)) listOf(this to listOf()) else listOf())
        }

        else -> {
          ops.flatMap { it.derefsWithShortCircuitCond }
        }
      }
}
