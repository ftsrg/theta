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

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr
import hu.bme.mit.theta.core.type.abstracttype.GtExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.TypeUtils.getDefaultValue
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.references

/** Removes all references in favor of creating arrays instead. */
class ReferenceElimination(val parseContext: ParseContext) : ProcedurePass {

  companion object {

    private var cnt = 2 // counts upwards, uses 3k+2
      get() = field.also { field += 3 }

    private val ptrVars: MutableMap<XcfaBuilder, VarDecl<*>> = mutableMapOf()

    private fun XcfaBuilder.ptrVar(parseContext: ParseContext) =
      ptrVars.getOrPut(this) { Var("__sp", CPointer(null, null, parseContext).smtType) }
  }

  private lateinit var currentBuilder: XcfaProcedureBuilder
  private var tmpRefCnt = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    currentBuilder = builder
    val references =
      builder.getEdges().flatMap { it.label.getFlatLabels().flatMap { it.references } }

    // Case 1: no reference concerns this procedure, so this pass must be a no-op.
    // A global referred in *another* procedure concerns us even without a local reference:
    // every access to it must go through the shared dereference, and the init procedure
    // must seed the pointer variables (e.g. `main` calling pthread_create on a thread whose
    // body takes `&y` — the `&t` handle was already consumed by CLibraryFunctionsPass).
    if (references.isEmpty() && globalReferredVars(builder).isEmpty()) return builder

    // Case 2: simple elimination first.
    // Summary: for references to VarDecls (`(ref x)`), keep the old behavior:
    // - create synthetic pointer variable `x*`
    // - replace each use of `x` with `(deref x* 0)`
    // - replace `(ref x)` with `x*`
    val simpleChanged = runSimpleReferenceElimination(builder)

    // Case 3: complex elimination second.
    // Summary: for references to dereferences (`(ref (deref B O))`), keep base/offset pairs
    // explicit:
    // - normalize nested ref-to-deref occurrences with temporary vars
    // - split pointer-carrying vars to `<v>_base` and `<v>_offset`
    // - rewrite dereferences through split vars to `(deref v_base (+ v_offset off))`
    val complexChanged = runComplexReferenceElimination(builder)

    if (simpleChanged || complexChanged) {
      return DeterministicPass().run(NormalizePass().run(builder))
    }
    return builder
  }

  @Suppress("UNCHECKED_CAST")
  private fun globalReferredVars(
    builder: XcfaProcedureBuilder
  ): Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>> {
    val globalReferredVars =
      builder.parent.metaData.computeIfAbsent("references") {
        builder.parent
          .getProcedures()
          .flatMap { p ->
            p.getEdges().flatMap { it -> it.label.getFlatLabels().flatMap { it.references } }
          }
          .mapNotNull(::getDirectReferencedDecl)
          .toSet()
          .filter { builder.parent.getVars().any { global -> global.wrappedVar == it } }
          .associateWith {
            val ptrType = CPointer(null, CComplexType.getType(it.ref, parseContext), parseContext)
            val varDecl = Var(it.name + "*", ptrType.smtType)
            val lit = CComplexType.getType(varDecl.ref, parseContext).getValue("$cnt")
            // Taking the address of an `_Atomic` variable does not make it any less atomic: every
            // access to it now goes through this pointer, so the pointer has to carry the fact.
            builder.parent.addVar(
              XcfaGlobalVar(varDecl, lit, pointsToAtomic = ptrType.embeddedType.isAtomic)
            )
            parseContext.metadata.create(varDecl.ref, "cType", ptrType)
            val assign = AssignStmtLabel(varDecl, lit)
            val labels =
              if (MemsafetyPass.enabled) {
                val assign2 =
                  builder.parent.allocateReferenced(
                    parseContext,
                    varDecl.ref,
                    ptrType.embeddedType,
                  )

                listOf(assign, assign2)
              } else {
                listOf(assign)
              }
            Pair(varDecl, SequenceLabel(labels))
          }
      }
    checkState(globalReferredVars is Map<*, *>, "ReferenceElimination needs info on references")
    return globalReferredVars as Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>>
  }

  private fun runSimpleReferenceElimination(builder: XcfaProcedureBuilder): Boolean {
    val ptrVar = builder.parent.ptrVar(parseContext)
    val globalReferredVars = globalReferredVars(builder)

    val referredVars =
      builder
        .getEdges()
        .flatMap { e -> e.label.getFlatLabels().flatMap { it.references } }
        .mapNotNull(::getDirectReferencedDecl)
        .toSet()
        .filter { !globalReferredVars.containsKey(it) }
        .associateWith { v ->
          val ptrType = CPointer(null, CComplexType.getType(v.ref, parseContext), parseContext)

          if (builder.parent.getVars().none { it.wrappedVar == ptrVar }) { // initial creation
            val initVal = ptrType.getValue("$cnt")
            builder.parent.addVar(XcfaGlobalVar(ptrVar, initVal, atomic = true))
            val initProc = builder.parent.getInitProcedures().map { it.first }
            checkState(initProc.size == 1, "Multiple start procedure are not handled well")
            initProc.forEach { proc ->
              val initAssign = AssignStmtLabel(ptrVar, initVal)
              val newEdges =
                proc.initLoc.outgoingEdges.map {
                  it.withLabel(
                    SequenceLabel(listOf(initAssign) + it.label.getFlatLabels(), it.label.metadata)
                  )
                }
              proc.initLoc.outgoingEdges.forEach(proc::removeEdge)
              newEdges.forEach(proc::addEdge)
            }
          }
          val assign1 =
            AssignStmtLabel(ptrVar, Add(ptrVar.ref, ptrType.getValue("3")), ptrType.smtType)
          val varDecl = Var(v.name + "*", ptrType.smtType)
          builder.addVar(varDecl)
          parseContext.metadata.create(varDecl.ref, "cType", ptrType)
          val assign2 = AssignStmtLabel(varDecl, ptrVar.ref)
          val labels =
            if (MemsafetyPass.enabled) {
              val assign3 =
                builder.parent.allocateReferenced(parseContext, varDecl.ref, ptrType.embeddedType)

              listOf(assign1, assign2, assign3)
            } else {
              listOf(assign1, assign2)
            }
          Pair(varDecl, SequenceLabel(labels))
        }

    val allReferredVars = referredVars + globalReferredVars
    if (allReferredVars.isNotEmpty()) {
      val edges = LinkedHashSet(builder.getEdges())
      for (edge in edges) {
        builder.removeEdge(edge)
        builder.addEdge(
          edge.withLabel(edge.label.changeReferredVars(allReferredVars, parseContext))
        )
      }
      if (builder.parent.getInitProcedures().any { it.first == builder }) {
        addRefInitializations(builder, globalReferredVars) // we only need this for main
      }
      addRefInitializations(builder, referredVars)
      return true
    }
    return false
  }

  private fun addRefInitializations(
    builder: XcfaProcedureBuilder,
    referredVars: Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>>,
  ) {
    if (referredVars.isEmpty()) return
    val initLabels = referredVars.values.flatMap { it.second.labels }
    val initEdges = builder.initLoc.outgoingEdges
    val newInitEdges =
      initEdges.map {
        val labels = it.label.getFlatLabels()
        val sizeInit =
          labels.find {
            it is StmtLabel &&
              it.stmt is AssignStmt<*> &&
              it.stmt.varDecl.let { it.name == "__theta_ptr_size" && it.type is ArrayType<*, *> } &&
              it.stmt.expr is ArrayLitExpr<*, *>
          }
        val spInit =
          labels.find {
            it is StmtLabel &&
              it.stmt is AssignStmt<*> &&
              it.stmt.varDecl == builder.parent.ptrVar(parseContext)
          }
        val touchedParams =
          builder.getParams().filter {
            it.second != ParamDirection.OUT && referredVars.containsKey(it.first)
          }
        val paramMapping =
          if (touchedParams.isNotEmpty()) {
            touchedParams.map {
              val type = referredVars[it.first]!!.first.type
              StmtLabel(
                MemoryAssignStmt.create(
                  Dereference(
                    cast(referredVars[it.first]!!.first.ref, type),
                    cast(CComplexType.getSignedLong(parseContext).nullValue, type),
                    it.first.type,
                  ),
                  it.first.ref,
                )
              )
            }
          } else listOf()
        val newLabelOrder =
          listOfNotNull(spInit) +
            listOfNotNull(sizeInit) +
            initLabels +
            paramMapping +
            labels.filter { it != sizeInit && it != spInit }
        it.withLabel(SequenceLabel(newLabelOrder, it.label.metadata))
      }
    initEdges.forEach(builder::removeEdge)
    newInitEdges.forEach(builder::addEdge)
  }

  private fun getDirectReferencedDecl(reference: Reference<*, *>): VarDecl<*>? =
    (reference.expr as? RefExpr<*>)?.decl as? VarDecl<*>

  /**
   * The number of flat cells an object of [type] occupies, or null when it is not statically sized
   * (a VLA or a flexible array member). An array multiplies its constant dimensions through its
   * element's cell count -- matching `FrontendXcfaBuilder.flatArraySize` and
   * `ExpressionVisitor#rowOf`, which lay `int a[3][4]` out as twelve cells `arrays[a][i*4 + j]`.
   */
  private fun flatCellCount(type: CComplexType): Int? =
    when (type) {
      is CArray -> {
        val dim = ObjectLayout.constantDimension(type) ?: return null
        val elem = flatCellCount(type.embeddedType) ?: return null
        dim * elem
      }
      is CStruct -> if (type.isUnion) 1 else type.unitCount
      else -> 1
    }

  /**
   * Sizes the object a taken address points to. An array is aliased with its own first element
   * (`&a == a == &a[0]`), so the pointer the reference machinery hands out has to span the array's
   * cells, not one: allocating a single unit made `arr[i]` for any `i > 0` -- reached through
   * `(int **)&arr` and the like -- a spurious out-of-bounds `valid-deref`. A struct keeps its
   * historical one-cell-per-field size; a scalar is one cell.
   */
  private fun XcfaBuilder.allocateReferenced(
    parseContext: ParseContext,
    base: Expr<*>,
    embeddedType: CComplexType,
  ): StmtLabel {
    val cells =
      when (embeddedType) {
        is CStruct -> if (embeddedType.isUnion) 1 else embeddedType.fields.size
        is CArray -> flatCellCount(embeddedType)
        else -> 1
      }
    return if (cells != null)
      allocate(parseContext, base, Fitsall(null, parseContext).getValue("$cells"))
    else allocateUnit(parseContext, base)
  }

  private data class SplitVarPair(val base: VarDecl<Type>, val offset: VarDecl<Type>)

  private enum class SplitChannel {
    BASE,
    OFFSET,
  }

  /**
   * A pointer cast to a same-or-wider integer and back is a `Pos` no-op (the cast visitor's
   * width-preserving path emits no modulo), so a split pointer routed through an integer -- as CIL
   * does, `q = (unsigned long)p; ... (T *)q` -- arrives wrapped in `Pos`. Look through it to find
   * the split variable the base/offset machinery tracks.
   */
  private fun Expr<*>.stripPos(): Expr<*> = if (this is PosExpr<*>) op.stripPos() else this

  private fun runComplexReferenceElimination(builder: XcfaProcedureBuilder): Boolean {
    val hasRefToDeref =
      builder.getEdges().any { edge ->
        edge.label.getFlatLabels().flatMap { it.references }.any { it.expr is Dereference<*, *, *> }
      }
    if (!hasRefToDeref) return false

    var changed = normalizeNestedReferenceAssignments(builder)
    val splitVars = discoverSplitVars(builder)
    if (splitVars.isEmpty()) return changed
    val edges = LinkedHashSet(builder.getEdges())
    for (edge in edges) {
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(edge.label.changeComplexReferredVars(splitVars)))
    }
    seedSplitParams(builder, splitVars)
    return true
  }

  /**
   * A pointer parameter that gets split still enters the procedure as the single value the caller
   * bound to it. This pass runs per-procedure, *before* inlining, so it never sees that binding: it
   * splits the parameter `p` into `p_base`/`p_offset` and rewrites the body onto them, but nothing
   * ever gives them a value. Inlining then binds the (now unused) original `p`, leaving `p_base` and
   * `p_offset` unconstrained -- so the solver is free to pick an out-of-range offset and walk off the
   * object, a false `valid-deref` on every `str*`-style callee that increments its argument.
   *
   * Seed the halves at the procedure entry from the still-bound parameter: `p_base = p`, `p_offset =
   * 0`. The offset is zero because a pointer argument is a base id at offset 0 -- the model cannot
   * carry a mid-object pointer across a call (passing a bare split variable is rejected outright),
   * so whatever the caller binds to `p` is exactly the base.
   */
  private fun seedSplitParams(
    builder: XcfaProcedureBuilder,
    splitVars: Map<VarDecl<*>, SplitVarPair>,
  ) {
    val splitParams =
      builder.getParams().filter { it.second != ParamDirection.OUT && it.first in splitVars.keys }
    if (splitParams.isEmpty()) return
    val seeds =
      splitParams.flatMap { (param, _) ->
        val split = splitVars[param]!!
        listOf(
          AssignStmtLabel(split.base, param.ref, split.base.type),
          AssignStmtLabel(
            split.offset,
            CComplexType.getSignedLong(parseContext).nullValue,
            split.offset.type,
          ),
        )
      }
    val initEdges = builder.initLoc.outgoingEdges.toList()
    val newEdges =
      initEdges.map {
        it.withLabel(SequenceLabel(seeds + it.label.getFlatLabels(), it.label.metadata))
      }
    initEdges.forEach(builder::removeEdge)
    newEdges.forEach(builder::addEdge)
  }

  private fun normalizeNestedReferenceAssignments(builder: XcfaProcedureBuilder): Boolean {
    var changed = false
    val edges = LinkedHashSet(builder.getEdges())
    for (edge in edges) {
      val rewritten = edge.label.normalizeNestedReferenceAssignments(builder)
      if (rewritten != edge.label) {
        changed = true
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(rewritten))
      }
    }
    return changed
  }

  private fun discoverSplitVars(
    builder: XcfaProcedureBuilder
  ): MutableMap<VarDecl<*>, SplitVarPair> {
    val splitVars = linkedMapOf<VarDecl<*>, SplitVarPair>()
    var changed: Boolean
    do {
      changed = false
      builder.getEdges().forEach { edge ->
        edge.label.getFlatLabels().forEach { label ->
          if (label is StmtLabel && label.stmt is AssignStmt<*>) {
            val stmt = label.stmt as AssignStmt<*>
            val lhs = stmt.varDecl
            val rhs = stmt.expr
            when {
              rhs is Reference<*, *> && rhs.expr is Dereference<*, *, *> -> {
                val deref = rhs.expr as Dereference<*, *, *>
                changed =
                  ensureSplitVar(builder, splitVars, lhs, deref.array.type, deref.offset.type) ||
                    changed
              }
              rhs.stripPos().let { it is RefExpr<*> && it.decl in splitVars.keys } -> {
                val src = splitVars[(rhs.stripPos() as RefExpr<*>).decl]!!
                changed =
                  ensureSplitVar(builder, splitVars, lhs, src.base.type, src.offset.type) || changed
              }
            }
          }
        }
      }
    } while (changed)
    return splitVars
  }

  private fun ensureSplitVar(
    builder: XcfaProcedureBuilder,
    splitVars: MutableMap<VarDecl<*>, SplitVarPair>,
    original: VarDecl<*>,
    baseType: Type,
    offsetType: Type,
  ): Boolean {
    val existing = splitVars[original]
    if (existing != null) {
      checkState(
        existing.base.type == baseType,
        "Inconsistent base type for split var ${original.name}",
      )
      checkState(
        existing.offset.type == offsetType,
        "Inconsistent offset type for split var ${original.name}",
      )
      return false
    }

    val baseVar = Var("${original.name}_base", baseType)
    val offsetVar = Var("${original.name}_offset", offsetType)
    val isGlobal = builder.parent.getVars().any { it.wrappedVar == original }
    if (isGlobal) {
      if (builder.parent.getVars().none { it.wrappedVar == baseVar }) {
        builder.parent.addVar(XcfaGlobalVar(baseVar))
      }
      if (builder.parent.getVars().none { it.wrappedVar == offsetVar }) {
        builder.parent.addVar(XcfaGlobalVar(offsetVar))
      }
    } else {
      if (builder.getVars().none { it == baseVar }) builder.addVar(baseVar)
      if (builder.getVars().none { it == offsetVar }) builder.addVar(offsetVar)
    }
    splitVars[original] = SplitVarPair(baseVar, offsetVar)
    return true
  }

  private fun XcfaLabel.normalizeNestedReferenceAssignments(
    builder: XcfaProcedureBuilder
  ): XcfaLabel =
    when (this) {
      is InvokeLabel -> this
      is NondetLabel ->
        NondetLabel(
          labels.map { it.normalizeNestedReferenceAssignments(builder) }.toSet(),
          metadata,
        )
      is SequenceLabel ->
        SequenceLabel(labels.map { it.normalizeNestedReferenceAssignments(builder) }, metadata)
      is StartLabel -> this
      is StmtLabel -> {
        val stmts = stmt.normalizeNestedReferenceAssignments(builder)
        SequenceLabel(stmts.map { StmtLabel(it, metadata = metadata, choiceType = choiceType) })
          .let { if (it.labels.size == 1) it.labels[0] else it }
      }
      else -> this
    }

  private fun Stmt.normalizeNestedReferenceAssignments(builder: XcfaProcedureBuilder): List<Stmt> {
    when (this) {
      is AssignStmt<*> -> {
        val rhs = this.expr
        val nestedRefs = rhs.collectRefToDerefExprs().toMutableList()
        if (nestedRefs.isEmpty()) return listOf(this)
        if (rhs is Reference<*, *> && rhs.expr is Dereference<*, *, *>) return listOf(this)

        val replacements = linkedMapOf<Reference<*, *>, Expr<*>>()
        val preAssigns = mutableListOf<Stmt>()
        nestedRefs.forEach { refExpr ->
          val tmp = Var("__theta_ref_tmp_${tmpRefCnt++}", refExpr.type)
          builder.addVar(tmp)
          replacements[refExpr] = tmp.ref
          preAssigns += AssignStmt.of(cast(tmp, tmp.type), cast(refExpr, tmp.type))
        }
        val newRhs = rhs.replaceRefExprs(replacements)
        val newAssign =
          AssignStmt.of(cast(this.varDecl, this.varDecl.type), cast(newRhs, this.varDecl.type))
        return preAssigns + newAssign
      }

      is MemoryAssignStmt<*, *, *> -> {
        val nestedRefs =
          (deref.collectRefToDerefExprs() + expr.collectRefToDerefExprs()).toMutableList()
        if (nestedRefs.isEmpty()) return listOf(this)

        val replacements = linkedMapOf<Reference<*, *>, Expr<*>>()
        val preAssigns = mutableListOf<Stmt>()
        nestedRefs.forEach { refExpr ->
          val tmp = Var("__theta_ref_tmp_${tmpRefCnt++}", refExpr.type)
          builder.addVar(tmp)
          replacements[refExpr] = tmp.ref
          preAssigns += AssignStmt.of(cast(tmp, tmp.type), cast(refExpr, tmp.type))
        }
        val newDeref = deref.replaceRefExprs(replacements)
        val newExpr = expr.replaceRefExprs(replacements)
        return preAssigns + MemoryAssignStmt.create(newDeref as Dereference<*, *, *>, newExpr)
      }

      is AssumeStmt -> {
        val nestedRefs = cond.collectRefToDerefExprs().toMutableList()
        if (nestedRefs.isEmpty()) return listOf(this)

        val replacements = linkedMapOf<Reference<*, *>, Expr<*>>()
        val preAssigns = mutableListOf<Stmt>()
        nestedRefs.forEach { refExpr ->
          val tmp = Var("__theta_ref_tmp_${tmpRefCnt++}", refExpr.type)
          builder.addVar(tmp)
          replacements[refExpr] = tmp.ref
          preAssigns += AssignStmt.of(cast(tmp, tmp.type), cast(refExpr, tmp.type))
        }
        return preAssigns + AssumeStmt.of(cast(cond.replaceRefExprs(replacements), cond.type))
      }

      else -> return listOf(this)
    }
  }

  private fun Expr<*>.collectRefToDerefExprs(): List<Reference<*, *>> {
    val nested = ops.flatMap { it.collectRefToDerefExprs() }
    return if (this is Reference<*, *> && this.expr is Dereference<*, *, *>) listOf(this) + nested
    else nested
  }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.replaceRefExprs(
    replacements: Map<Reference<*, *>, Expr<*>>
  ): Expr<T> {
    val direct = (this as? Reference<*, *>)?.let { replacements[it] }
    if (direct != null) return cast(direct, this.type)
    return this.withOps(this.ops.map { (it as Expr<Type>).replaceRefExprs(replacements) })
      as Expr<T>
  }

  private fun XcfaLabel.changeComplexReferredVars(
    splitVars: Map<VarDecl<*>, SplitVarPair>
  ): XcfaLabel =
    when (this) {
      is InvokeLabel ->
        InvokeLabel(
          name = name,
          params = params.map { it.changeComplexReferredVars(splitVars) },
          metadata = metadata,
          tempLookup = tempLookup,
          isLibraryFunction = isLibraryFunction,
        )
      is NondetLabel ->
        NondetLabel(labels.map { it.changeComplexReferredVars(splitVars) }.toSet(), metadata)
      is SequenceLabel ->
        SequenceLabel(labels.map { it.changeComplexReferredVars(splitVars) }, metadata)
      is StartLabel ->
        StartLabel(name, params.map { it.changeComplexReferredVars(splitVars) }, pidVar, metadata)
      is StmtLabel ->
        SequenceLabel(
            stmt.changeComplexReferredVars(splitVars).map {
              StmtLabel(it, metadata = metadata, choiceType = choiceType)
            }
          )
          .let { if (it.labels.size == 1) it.labels[0] else it }
      else -> this
    }

  private fun Stmt.changeComplexReferredVars(splitVars: Map<VarDecl<*>, SplitVarPair>): List<Stmt> =
    when (this) {
      is AssignStmt<*> -> changeComplexAssign(splitVars)
      is MemoryAssignStmt<*, *, *> -> {
        // A split variable in the stored *value* is a pointer being written to memory, whose base
        // and offset go to two separate memory channels. A split variable in the *address* is only
        // the pointer we write through: `deref.changeComplexReferredVars` (below) already folds it
        // to `deref(base, offset)`, so it must not be channel-split -- otherwise `*p = 5` would
        // write to both `p_base[0]` and `deref(p_offset, 0)` (i.e. to whatever object id the offset
        // happens to equal) instead of the single cell `deref(p_base, p_offset)`.
        val hasSplitRefs = expr.containsSplitRefs(splitVars)

        if (hasSplitRefs) {
          val baseDeref =
            deref
              .replaceSplitRefs(splitVars, SplitChannel.BASE)
              .changeComplexReferredVars(splitVars) as Dereference<*, *, *>
          val baseExpr =
            expr.replaceSplitRefs(splitVars, SplitChannel.BASE).changeComplexReferredVars(splitVars)

          val offsetDeref =
            deref
              .replaceSplitRefs(splitVars, SplitChannel.OFFSET)
              .changeComplexReferredVars(splitVars) as Dereference<*, *, *>
          val offsetExpr =
            expr
              .replaceSplitRefs(splitVars, SplitChannel.OFFSET)
              .changeComplexReferredVars(splitVars)

          listOf(
            MemoryAssignStmt.create(baseDeref, baseExpr),
            MemoryAssignStmt.create(offsetDeref, offsetExpr),
          )
        } else {
          listOf(
            MemoryAssignStmt.create(
              deref.changeComplexReferredVars(splitVars) as Dereference<*, *, *>,
              expr.changeComplexReferredVars(splitVars),
            )
          )
        }
      }
      is AssumeStmt -> listOf(AssumeStmt.of(cond.changeComplexReferredVars(splitVars)))
      is SequenceStmt ->
        listOf(SequenceStmt.of(stmts.flatMap { it.changeComplexReferredVars(splitVars) }))
      is SkipStmt -> listOf(this)
      else -> TODO("Not yet implemented ($this)")
    }

  private fun Expr<*>.containsSplitRefs(splitVars: Map<VarDecl<*>, SplitVarPair>): Boolean =
    when {
      this is RefExpr<*> -> this.decl in splitVars.keys
      // A dereference reads a value *through* a pointer. A split var in its address is the pointer we
      // read through -- the deref rewriting folds it to `deref(base, offset)` -- not a pointer *value*
      // being stored, and the value it reads is a single memory cell (a scalar, for `*to = *from`; a
      // single base id for a pointer in memory), never a split var. Recursing into it counted the
      // address as if it were a stored pointer, so `*to = *from` (a char copy through two split
      // pointers) was wrongly channel-split into `arrays[to_offset][…] := arrays[from_offset][…]`,
      // whose bounds check then read `ptr_size[offset]` -- unallocated -- and false-alarmed.
      this is Dereference<*, *, *> -> false
      else -> this.ops.any { (it as Expr<Type>).containsSplitRefs(splitVars) }
    }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.replaceSplitRefs(
    splitVars: Map<VarDecl<*>, SplitVarPair>,
    channel: SplitChannel,
  ): Expr<T> {
    if (this is RefExpr<*> && this.decl in splitVars.keys) {
      val split = splitVars[this.decl]!!
      val replacement = if (channel == SplitChannel.BASE) split.base.ref else split.offset.ref
      return cast(replacement, this.type)
    }

    val ret = this.withOps(this.ops.map { (it as Expr<Type>).replaceSplitRefs(splitVars, channel) })
    return ret as Expr<T>
  }

  @Suppress("UNCHECKED_CAST")
  private fun AssignStmt<*>.changeComplexAssign(
    splitVars: Map<VarDecl<*>, SplitVarPair>
  ): List<Stmt> {
    val lhs = varDecl
    val rhs = expr
    if (rhs is Reference<*, *> && rhs.expr is Dereference<*, *, *>) {
      val split = splitVars[lhs] ?: error("Split vars not found for ${lhs.name}")
      val deref = rhs.expr as Dereference<*, *, *>
      val array = deref.array
      val offsetExpr = deref.offset.changeComplexReferredVars(splitVars)
      if (array is RefExpr<*> && array.decl in splitVars.keys) {
        // Chained pointer arithmetic: the base is itself a split pointer, as in `p = q + i` after
        // `q = r + j`. Compose rather than re-address -- `p_base = q_base`, `p_offset = q_offset +
        // i` -- so the offset accumulates instead of the bare split `q` being used as an address.
        val src = splitVars[array.decl]!!
        return listOf(
          AssignStmt.of(cast(split.base, split.base.type), cast(src.base.ref, split.base.type)),
          AssignStmt.of(
            cast(split.offset, split.offset.type),
            cast(
              Add(cast(src.offset.ref, split.offset.type), cast(offsetExpr, split.offset.type)),
              split.offset.type,
            ),
          ),
        )
      }
      val baseExpr = array.changeComplexReferredVars(splitVars)
      return listOf(
        AssignStmt.of(cast(split.base, split.base.type), cast(baseExpr, split.base.type)),
        AssignStmt.of(cast(split.offset, split.offset.type), cast(offsetExpr, split.offset.type)),
      )
    }
    val strippedRhs = rhs.stripPos()
    if (strippedRhs is RefExpr<*> && strippedRhs.decl in splitVars.keys) {
      // A plain copy, or the same pointer routed through a width-preserving integer cast (which the
      // cast visitor leaves as a `Pos` no-op): the base and the offset travel together.
      val src = splitVars[strippedRhs.decl]!!
      val dst = splitVars[lhs] ?: error("Split vars not found for ${lhs.name}")
      return listOf(
        AssignStmt.of(cast(dst.base, dst.base.type), cast(src.base.ref, dst.base.type)),
        AssignStmt.of(cast(dst.offset, dst.offset.type), cast(src.offset.ref, dst.offset.type)),
      )
    }
    if (lhs in splitVars.keys) {
      // Only a *flat* pointer value: a plain (never-split) variable, or a literal such as `NULL`.
      // Deliberately NOT a dereference: `p = *q` loads a pointer that was *stored* to memory, and
      // storing a split pointer writes base and offset to two separate channels (see the
      // MemoryAssignStmt case). Reading only the base back and forcing the offset to 0 would
      // silently drop a stored mid-object offset and address the wrong cell, so that case keeps
      // failing loudly instead.
      val flatPointerValue =
        !rhs.containsSplitRefs(splitVars) &&
          (strippedRhs is RefExpr<*> || strippedRhs is LitExpr<*>)
      if (flatPointerValue) {
        // `p = s` where `p` became split (through later arithmetic) but `s` never did: a plain
        // pointer value is a base id at offset 0. Seed the halves accordingly -- `p_base = s`,
        // `p_offset = 0` -- so the later `p++`/`p - s` operate on a well-defined origin. This is the
        // same shape `seedSplitParams` gives a pointer parameter, applied to a local copy. A null
        // pointer (`p = 0`) lands here too and is correctly (base 0, offset 0).
        val dst = splitVars[lhs]!!
        val baseExpr = rhs.changeComplexReferredVars(splitVars)
        return listOf(
          AssignStmt.of(cast(dst.base, dst.base.type), cast(baseExpr, dst.base.type)),
          AssignStmt.of(
            cast(dst.offset, dst.offset.type),
            cast(getDefaultValue(dst.offset.type), dst.offset.type),
          ),
        )
      }
      error("Unsupported pointer arithmetic: assignment to split pointer variable ${lhs.name}")
    }
    val rewrittenRhs = rhs.changeComplexReferredVars(splitVars)
    return listOf(AssignStmt.of(cast(lhs, lhs.type), cast(rewrittenRhs, lhs.type)))
  }

  private fun Expr<*>.splitPairOf(splitVars: Map<VarDecl<*>, SplitVarPair>): SplitVarPair? {
    val resolved = stripPos()
    return if (resolved is RefExpr<*> && resolved.decl in splitVars.keys) splitVars[resolved.decl]
    else null
  }

  /**
   * The base-id channel of an operand in a pointer comparison. A split pointer contributes its own
   * `base`; anything else -- a null literal, or a plain pointer/array variable that was never split
   * -- denotes a base id at offset 0, so it contributes its (rewritten) value.
   */
  private fun Expr<*>.pointerBaseChannel(
    splitVars: Map<VarDecl<*>, SplitVarPair>,
    baseType: Type,
  ): Expr<*> {
    val split = splitPairOf(splitVars)
    return if (split != null) cast(split.base.ref, baseType)
    else cast(this.changeComplexReferredVars(splitVars), baseType)
  }

  /**
   * The offset channel of an operand in a pointer comparison or difference. A split pointer
   * contributes its `offset`; a plain pointer value is at offset 0.
   */
  private fun Expr<*>.pointerOffsetChannel(
    splitVars: Map<VarDecl<*>, SplitVarPair>,
    offsetType: Type,
  ): Expr<*> {
    val split = splitPairOf(splitVars)
    return if (split != null) cast(split.offset.ref, offsetType) else getDefaultValue(offsetType)
  }

  /**
   * Uses of a split pointer that stay *scalar* -- a comparison or a pointer difference -- rather than
   * dereferencing or re-addressing it. The split model keeps a pointer as `(base, offset)`, so:
   * - `p == q` is `base_p == base_q && off_p == off_q` (well-defined across objects: two pointers
   *   into different objects compare unequal), and `!=` is its negation;
   * - `p < q` (and `<=`, `>`, `>=`) is defined by C only within one object, so it is `off_p < off_q`
   *   -- a different-object comparison is undefined and any answer is sound;
   * - `p - q` is `off_p - off_q`, in element units, exactly what the offset already counts (each
   *   `p++` advances the offset by one element). The frontend spells a difference as an `Add` whose
   *   split bases cancel (`Add(p, Neg(q))`, or `Add(p, Neg(1), Neg(s1))` for `p - 1 - s1`); a net
   *   non-zero base means a mid-object pointer *value* is escaping into a scalar context, which the
   *   split model cannot carry, so that falls through to the bare-use error.
   *
   * Returns the decomposed expression, or `null` when the shape is not one of these (so the caller
   * proceeds with its ordinary rewriting, including the loud refusal of an unsupported bare use).
   */
  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.decomposeScalarPointerOp(
    splitVars: Map<VarDecl<*>, SplitVarPair>
  ): Expr<T>? {
    if (
      this is EqExpr<*> ||
        this is NeqExpr<*> ||
        this is LtExpr<*> ||
        this is LeqExpr<*> ||
        this is GtExpr<*> ||
        this is GeqExpr<*>
    ) {
      val left = ops[0]
      val right = ops[1]
      val ref = left.splitPairOf(splitVars) ?: right.splitPairOf(splitVars) ?: return null
      val baseType = ref.base.type
      val offsetType = ref.offset.type
      val baseL = left.pointerBaseChannel(splitVars, baseType)
      val baseR = right.pointerBaseChannel(splitVars, baseType)
      val offL = left.pointerOffsetChannel(splitVars, offsetType)
      val offR = right.pointerOffsetChannel(splitVars, offsetType)
      // Ordering compares offsets only when BOTH sides are pointers -- that is the one case C
      // defines, and within an object the bases are equal. Against a plain integer it is not a
      // pointer-vs-pointer comparison at all but a constraint on the pointer *value*, most often the
      // range assume the frontend emits for a declaration (`0 <= us <= 4294967295`). Decomposing
      // that onto the offset read the integer bound as "a pointer at offset 0" and collapsed the
      // assume to `us_offset in [0,0]`, pinning the offset instead of stating a tautology. Such a
      // constraint belongs on the base, the pointer's principal component.
      val bothPointers = left.isPointerOperand(splitVars) && right.isPointerOperand(splitVars)
      val ordL = if (bothPointers) offL else baseL
      val ordR = if (bothPointers) offR else baseR
      val decomposed: Expr<BoolType> =
        when (this) {
          is EqExpr<*> -> And(Eq(baseL, baseR), Eq(offL, offR))
          is NeqExpr<*> -> Or(Neq(baseL, baseR), Neq(offL, offR))
          is LtExpr<*> -> Lt(ordL, ordR)
          is LeqExpr<*> -> Leq(ordL, ordR)
          is GtExpr<*> -> Gt(ordL, ordR)
          else -> Geq(ordL, ordR)
        }
      return cast(decomposed, this.type)
    }
    if (this is AddExpr<*>) {
      val signed =
        ops.map { op -> op.stripPos().let { if (it is NegExpr<*>) it.op to true else op to false } }
      // Only a *split* pointer forces a decomposition here; without one the ordinary rewriting is
      // fine (and a difference of two never-split pointers is not something this pass created).
      val split = signed.firstOrNull { it.first.splitPairOf(splitVars) != null } ?: return null
      // A difference is an Add whose pointer operands cancel: the bases drop out and only the
      // element offsets remain. A net non-zero base means a mid-object pointer *value* is escaping
      // into a scalar context, which the split model cannot carry -- fall through to the bare-use
      // error rather than silently dropping the base.
      val pointerTerms = signed.filter { it.first.isPointerOperand(splitVars) }
      if (pointerTerms.count { !it.second } != pointerTerms.count { it.second }) return null
      val offsetType = split.first.splitPairOf(splitVars)!!.offset.type
      val summands =
        signed.map { (term, negative) ->
          // A split pointer contributes its offset; a plain pointer sits at offset 0; a plain
          // integer term (`- 1`) contributes its own value.
          val channel =
            when {
              term.splitPairOf(splitVars) != null ->
                cast(term.splitPairOf(splitVars)!!.offset.ref, offsetType)
              term.isPointerOperand(splitVars) -> getDefaultValue(offsetType)
              else -> cast(term.changeComplexReferredVars(splitVars), offsetType)
            }
          if (negative) Neg(channel) else channel
        }
      return cast(Add(summands), this.type) as Expr<T>
    }
    return null
  }

  /**
   * Whether an operand denotes a pointer value: a split pointer, or a plain variable declared with a
   * pointer/array C type. Used to decide which operands of an `Add` are the bases that must cancel
   * for it to be a scalar pointer difference.
   */
  private fun Expr<*>.isPointerOperand(splitVars: Map<VarDecl<*>, SplitVarPair>): Boolean {
    if (splitPairOf(splitVars) != null) return true
    val resolved = stripPos()
    if (resolved is RefExpr<*>) {
      val cType = CComplexType.getType((resolved.decl as VarDecl<*>).ref, parseContext)
      return cType is CPointer || cType is CArray
    }
    return false
  }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.changeComplexReferredVars(
    splitVars: Map<VarDecl<*>, SplitVarPair>
  ): Expr<T> {
    decomposeScalarPointerOp(splitVars)?.let {
      return it
    }
    if (this is RefExpr<*> && this.decl in splitVars.keys) {
      error("Unsupported pointer arithmetic: bare use of split variable ${this.decl.name}")
    }
    if (this is Dereference<*, *, *>) {
      // The address may have come back through a width-preserving integer cast (`*(T *)q` after
      // `q = (unsigned long)p`), which the cast visitor leaves as a `Pos` no-op.
      val arr = this.array.stripPos()
      val rewrittenOffset = this.offset.changeComplexReferredVars(splitVars)
      if (arr is Reference<*, *> && arr.expr is Dereference<*, *, *>) {
        val innerDeref = arr.expr as Dereference<*, *, *>
        val rewrittenBase = innerDeref.array.changeComplexReferredVars(splitVars)
        val rewrittenInnerOffset = innerDeref.offset.changeComplexReferredVars(splitVars)
        val newOffset =
          Add(
            cast(rewrittenInnerOffset, innerDeref.offset.type),
            cast(rewrittenOffset, innerDeref.offset.type),
          )
        return Dereference(
          cast(rewrittenBase, innerDeref.array.type),
          cast(newOffset, innerDeref.offset.type),
          this.type,
        )
          as Expr<T>
      }
      if (arr is RefExpr<*> && arr.decl in splitVars.keys) {
        val split = splitVars[arr.decl]!!
        val newOffset =
          Add(cast(split.offset.ref, split.offset.type), cast(rewrittenOffset, split.offset.type))
        return Dereference(
          cast(split.base.ref, split.base.type),
          cast(newOffset, split.offset.type),
          this.type,
        )
          as Expr<T>
      }
      val rewrittenArray = arr.changeComplexReferredVars(splitVars)
      return this.withOps(listOf(rewrittenArray, rewrittenOffset)) as Expr<T>
    }
    val ret = this.withOps(this.ops.map { (it as Expr<Type>).changeComplexReferredVars(splitVars) })
    return ret as Expr<T>
  }

  @JvmOverloads
  fun XcfaLabel.changeReferredVars(
    varLut: Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>>,
    parseContext: ParseContext,
  ): XcfaLabel =
    if (varLut.isNotEmpty())
      when (this) {
        is InvokeLabel ->
          InvokeLabel(
            name,
            params.map { it.changeReferredVars(varLut, parseContext) },
            metadata = metadata,
            isLibraryFunction = isLibraryFunction,
          )

        is NondetLabel ->
          NondetLabel(
            labels.map { it.changeReferredVars(varLut, parseContext) }.toSet(),
            metadata = metadata,
          )

        is SequenceLabel ->
          SequenceLabel(
            labels.map { it.changeReferredVars(varLut, parseContext) },
            metadata = metadata,
          )

        is StartLabel ->
          StartLabel(
            name,
            params.map { it.changeReferredVars(varLut, parseContext) },
            pidVar,
            metadata = metadata,
          )

        is StmtLabel ->
          SequenceLabel(
              stmt.changeReferredVars(varLut, parseContext).map {
                StmtLabel(it, metadata = metadata, choiceType = this.choiceType)
              }
            )
            .let { if (it.labels.size == 1) it.labels[0] else it }

        else -> this
      }
    else this

  @JvmOverloads
  fun Stmt.changeReferredVars(
    varLut: Map<VarDecl<*>, Pair<VarDecl<Type>, XcfaLabel>>,
    parseContext: ParseContext,
  ): List<Stmt> {
    val stmts =
      when (this) {
        is AssignStmt<*> ->
          if (this.varDecl in varLut.keys) {
            val newVar = varLut[this.varDecl]!!.first
            val deref =
              Dereference(
                cast(newVar.ref, newVar.type),
                cast(CComplexType.getSignedLong(parseContext).nullValue, newVar.type),
                this.expr.type,
              )
            listOf(
              MemoryAssignStmt.create(deref, this.expr.changeReferredVars(varLut, parseContext))
            )
          } else {
            listOf(
              AssignStmt.of(
                cast(this.varDecl, this.varDecl.type),
                cast(this.expr.changeReferredVars(varLut, parseContext), this.varDecl.type),
              )
            )
          }

        is MemoryAssignStmt<*, *, *> ->
          listOf(
            MemoryAssignStmt.create(
              deref.changeReferredVars(varLut, parseContext) as Dereference<*, *, *>,
              expr.changeReferredVars(varLut, parseContext),
            )
          )

        is AssumeStmt -> listOf(AssumeStmt.of(cond.changeReferredVars(varLut, parseContext)))
        is SequenceStmt ->
          listOf(
            SequenceStmt.of(this.stmts.flatMap { it.changeReferredVars(varLut, parseContext) })
          )

        is SkipStmt -> listOf(this)
        else -> TODO("Not yet implemented ($this)")
      }
    val metadataValue = parseContext?.metadata?.getMetadataValue(this, "sourceStatement")
    if (metadataValue?.isPresent == true) {
      for (stmt in stmts) {
        parseContext.metadata.create(stmt, "sourceStatement", metadataValue.get())
      }
    }
    return stmts
  }

  @JvmOverloads
  fun <T : Type> Expr<T>.changeReferredVars(
    varLut: Map<VarDecl<*>, Pair<VarDecl<Type>, XcfaLabel>>,
    parseContext: ParseContext? = null,
  ): Expr<T> =
    if (this is RefExpr<T>) {
      (decl as VarDecl<T>).changeReferredVars(varLut)
    } else if (this is Reference<*, *>) {
      when (val target = this.expr) {
        is RefExpr<*> ->
          (varLut[target.decl]?.first?.ref as? Expr<T>)
            ?: run {
              val ret = this.withOps(this.ops.map { it.changeReferredVars(varLut, parseContext) })
              if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
                parseContext.metadata.create(ret, "cType", CComplexType.getType(this, parseContext))
              }
              ret
            }

        else -> {
          val ret = this.withOps(this.ops.map { it.changeReferredVars(varLut, parseContext) })
          if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
            parseContext.metadata.create(ret, "cType", CComplexType.getType(this, parseContext))
          }
          ret
        }
      }
    } else {
      val ret = this.withOps(this.ops.map { it.changeReferredVars(varLut, parseContext) })
      if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
        parseContext.metadata?.create(ret, "cType", CComplexType.getType(this, parseContext))
      }
      ret
    }

  private fun <T : Type> VarDecl<T>.changeReferredVars(
    varLut: Map<VarDecl<*>, Pair<VarDecl<Type>, XcfaLabel>>
  ): Expr<T> =
    varLut[this]?.first?.let {
      val cType = CComplexType.getType(this.ref, parseContext)
      if (cType is CStruct || cType is CArray) {
        // Struct/array variables already denote their own base id (a struct variable's value IS
        // its base, see FrontendXcfaBuilder's ptrCnt init and
        // ExpressionVisitor#visitPostfixExpressionMemberAccess). A bare use of such a variable must
        // therefore resolve exactly like `&v` does above -- the referred-var pointer's raw value,
        // with no extra indirection -- so that `m.field` (Deref(m, i)) and `a->field` (a = &m,
        // Deref(a, i)) address the same cell.
        cast(it.ref, this.type)
      } else {
        Dereference(
          cast(it.ref, it.type),
          // The offset is an offset into the pointed-to object, so it is pointer-wide -- like at
          // every other pointer site here. `int` only happens to work under ILP32, where a pointer
          // is 32 bits too; under LP64 it is 32 bits against a 64-bit pointer, and since `cast` is
          // a checked cast rather than a conversion, every pointer dereference then fails.
          cast(CComplexType.getSignedLong(parseContext).nullValue, it.type),
          this.type,
        )
          as Expr<T>
      }
    } ?: this.ref
}
