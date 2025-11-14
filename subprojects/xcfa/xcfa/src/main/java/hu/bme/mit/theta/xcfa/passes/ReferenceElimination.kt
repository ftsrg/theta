/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    currentBuilder = builder
    val ptrVar = builder.parent.ptrVar(parseContext)
    val globalReferredVars =
      builder.parent.metaData.computeIfAbsent("references") {
        builder.parent
          .getProcedures()
          .flatMap { p ->
            p.getEdges().flatMap { it -> it.label.getFlatLabels().flatMap { it.references } }
          }
          .mapNotNull { (it.expr as? RefExpr<*>)?.decl as? VarDecl<*> }
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
        .mapNotNull { (it.expr as? RefExpr<*>)?.decl as? VarDecl<*> }
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

      return DeterministicPass().run(NormalizePass().run(builder))
    }

    return builder
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

  @JvmOverloads
  fun XcfaLabel.changeReferredVars(
    varLut: Map<VarDecl<*>, Pair<VarDecl<Type>, SequenceLabel>>,
    parseContext: ParseContext,
  ): XcfaLabel =
    if (varLut.isNotEmpty())
      when (this) {
        is InvokeLabel -> copy(params = params.map { it.changeReferredVars(varLut, parseContext) })

        is NondetLabel ->
          copy(labels = labels.map { it.changeReferredVars(varLut, parseContext) }.toSet())

        is SequenceLabel ->
          copy(labels = labels.map { it.changeReferredVars(varLut, parseContext) })

        is StartLabel ->
          copy(
            params = params.map { it.changeReferredVars(varLut, parseContext) },
            handle = handle.changeReferredVars(varLut, parseContext),
          )

        is JoinLabel -> copy(handle = handle.changeReferredVars(varLut, parseContext))

        is StmtLabel ->
          SequenceLabel(stmt.changeReferredVars(varLut, parseContext).map { copy(stmt = it) }).let {
            if (it.labels.size == 1) it.labels[0] else it
          }

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
    } else if (
      this is Reference<*, *> &&
        this.expr is RefExpr<*> &&
        (this.expr as RefExpr<*>).decl in varLut.keys
    ) {
      varLut[(this.expr as RefExpr<*>).decl]?.first?.ref as Expr<T>
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
        cast(CComplexType.getType(it.ref, parseContext).nullValue, it.type),
        this.type,
      )
        as Expr<T>
    } ?: this.ref
}
