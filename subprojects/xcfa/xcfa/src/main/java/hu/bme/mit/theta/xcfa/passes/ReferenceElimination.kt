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
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
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

    // Case 1: there are no references in the XCFA, so this pass must be a no-op.
    if (references.isEmpty()) return builder

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

  private fun runSimpleReferenceElimination(builder: XcfaProcedureBuilder): Boolean {
    val ptrVar = builder.parent.ptrVar(parseContext)
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
            builder.parent.addVar(XcfaGlobalVar(varDecl, lit))
            parseContext.metadata.create(varDecl.ref, "cType", ptrType)
            val assign = AssignStmtLabel(varDecl, lit)
            val labels =
              if (MemsafetyPass.enabled) {
                val t = ptrType.embeddedType
                val assign2 =
                  if (t is CStruct) {
                    val type = Fitsall(null, parseContext)
                    builder.parent.allocate(
                      parseContext,
                      varDecl.ref,
                      type.getValue("${t.fields.size}"),
                    )
                  } else {
                    builder.parent.allocateUnit(parseContext, varDecl.ref)
                  }

                listOf(assign, assign2)
              } else {
                listOf(assign)
              }
            Pair(varDecl, SequenceLabel(labels))
          }
      }
    checkState(globalReferredVars is Map<*, *>, "ReferenceElimination needs info on references")
    globalReferredVars as Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>>

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
              val assign3 = builder.parent.allocateUnit(parseContext, varDecl.ref)

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

  private data class SplitVarPair(val base: VarDecl<Type>, val offset: VarDecl<Type>)

  private enum class SplitChannel {
    BASE,
    OFFSET,
  }

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
    return true
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
              rhs is RefExpr<*> && rhs.decl in splitVars.keys -> {
                val src = splitVars[rhs.decl]!!
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
        val hasSplitRefs = deref.containsSplitRefs(splitVars) || expr.containsSplitRefs(splitVars)

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
    (this is RefExpr<*> && this.decl in splitVars.keys) ||
      this.ops.any { (it as Expr<Type>).containsSplitRefs(splitVars) }

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
      val baseExpr = deref.array.changeComplexReferredVars(splitVars)
      val offsetExpr = deref.offset.changeComplexReferredVars(splitVars)
      return listOf(
        AssignStmt.of(cast(split.base, split.base.type), cast(baseExpr, split.base.type)),
        AssignStmt.of(cast(split.offset, split.offset.type), cast(offsetExpr, split.offset.type)),
      )
    }
    if (rhs is RefExpr<*> && rhs.decl in splitVars.keys) {
      val src = splitVars[rhs.decl]!!
      val dst = splitVars[lhs] ?: error("Split vars not found for ${lhs.name}")
      return listOf(
        AssignStmt.of(cast(dst.base, dst.base.type), cast(src.base.ref, dst.base.type)),
        AssignStmt.of(cast(dst.offset, dst.offset.type), cast(src.offset.ref, dst.offset.type)),
      )
    }
    if (lhs in splitVars.keys) {
      error("Unsupported pointer arithmetic: assignment to split pointer variable ${lhs.name}")
    }
    val rewrittenRhs = rhs.changeComplexReferredVars(splitVars)
    return listOf(AssignStmt.of(cast(lhs, lhs.type), cast(rewrittenRhs, lhs.type)))
  }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.changeComplexReferredVars(
    splitVars: Map<VarDecl<*>, SplitVarPair>
  ): Expr<T> {
    if (this is RefExpr<*> && this.decl in splitVars.keys) {
      error("Unsupported pointer arithmetic: bare use of split variable ${this.decl.name}")
    }
    if (this is Dereference<*, *, *>) {
      val arr = this.array
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
      Dereference(
        cast(it.ref, it.type),
        cast(CComplexType.getSignedInt(parseContext).nullValue, it.type),
        this.type,
      )
        as Expr<T>
    } ?: this.ref
}
