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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.DereferenceAccessMap
import hu.bme.mit.theta.xcfa.utils.READ
import hu.bme.mit.theta.xcfa.utils.VarAccessMap
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.getPotentialRacingVars
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Reduces data race checking to reachability checking by adding write access flags for each global
 * variable write access, and checks for multiple access and each global variable access (writes and
 * reads).
 */
class DataRaceToReachabilityPass(private val property: XcfaProperty) : ProcedurePass {

  companion object {
    var enabled = false

    private var potentialRacingVars: Set<VarDecl<*>>? = null

    private val writeFlagVars = mutableMapOf<VarDecl<*>, VarDecl<IntType>>()
    private val readFlagVars = mutableMapOf<VarDecl<*>, VarDecl<IntType>>()
    private val VarDecl<*>.writeFlag: VarDecl<IntType>
      get() = writeFlagVars[this]!!

    private val VarDecl<*>.readFlag: VarDecl<IntType>
      get() = readFlagVars[this]!!

    private val derefArrayWriteFlagVar = Decls.Var("_deref_array_write", Int())
    private val derefOffsetWriteFlagVar = Decls.Var("_deref_offset_write", Int())
    private val derefArrayReadFlagVar = Decls.Var("_deref_array_read", Int())
    private val derefOffsetReadFlagVar = Decls.Var("_deref_offset_read", Int())
    private val Expr<*>.derefArrayWriteFlag: VarDecl<IntType>
      get() = derefArrayWriteFlagVar.also { check(type == Int()) }

    private val Expr<*>.derefOffsetWriteFlag: VarDecl<IntType>
      get() = derefOffsetWriteFlagVar.also { check(type == Int()) }

    private val Expr<*>.derefArrayReadFlag: VarDecl<IntType>
      get() = derefArrayReadFlagVar.also { check(type == Int()) }

    private val Expr<*>.derefOffsetReadFlag: VarDecl<IntType>
      get() = derefOffsetReadFlagVar.also { check(type == Int()) }
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled) return builder

    removeOriginalErrorEdges(builder)
    val potentialRacingVars = collectPotentialRacingVars(builder)
    val isInitialPhase = builder in builder.parent.getInitProcedures().map { it.first }
    val visitedLocations = mutableSetOf<XcfaLocation>()
    val locationsToVisit = mutableListOf(Triple(builder.initLoc, false, isInitialPhase))
    while (locationsToVisit.isNotEmpty()) {
      val (loc, incomingAtomic, isInitialPhase) = locationsToVisit.removeLast()
      var initialPhase = isInitialPhase
      if (loc in visitedLocations) continue
      visitedLocations.add(loc)
      if (loc.incomingEdges.size > 1) initialPhase = false

      val branching = loc.outgoingEdges.size > 1
      val allVarsToCheck = mutableSetOf<VarDecl<*>>()
      val allDereferencesToCheck = mutableSetOf<Dereference<*, *, *>>()

      loc.outgoingEdges.toSet().forEachIndexed { index0, edge ->
        var atomic = incomingAtomic
        var initial = initialPhase
        var anyChange = false
        val newLabels =
          edge.getFlatLabels().mapIndexed { index1, label ->
            val firstLabel = index1 == 0
            check(!branching || !firstLabel || (label is StmtLabel && label.stmt is AssumeStmt)) {
              "In branching, the first label must be an assume statement."
            }

            if (initial) {
              if (label is StartLabel) initial = false
              return@mapIndexed listOf(label) to null
            }
            if (label is AtomicBeginLabel) atomic = true
            if (label is AtomicEndLabel) atomic = false

            val vars = label.collectVarsWithAccessType().filter { it.key in potentialRacingVars }
            val dereferences = label.dereferencesWithAccessType

            if (vars.isEmpty() && dereferences.isEmpty()) return@mapIndexed listOf(label) to null
            anyChange = true

            if (branching && firstLabel) {
              vars.forEach { (v, access) ->
                check(!access.isWritten && access.isRead)
                allVarsToCheck.add(v)
              }
              dereferences.forEach { (dereference, access) ->
                check(!access.isWritten && access.isRead)
                allDereferencesToCheck.add(dereference)
              }
              return@mapIndexed getNewLabelsForAccesses(
                vars,
                dereferences,
                label,
                skipPreLabels = true,
              )
            }

            getNewLabelsForAccesses(vars, dereferences, label)
          }

        if (anyChange) {
          replaceEdge(builder, loc, edge, index0, newLabels)
        }

        locationsToVisit.add(Triple(edge.target, atomic, initial))
      }

      if (branching && (allVarsToCheck.isNotEmpty() || allDereferencesToCheck.isNotEmpty())) {
        val newLoc =
          XcfaLocation("${loc.name}_dr", metadata = loc.metadata).also { builder.addLoc(it) }
        builder.addLoc(newLoc)
        val (newLabels, errorLabel) =
          getNewLabelsForAccesses(
            allVarsToCheck.associateWith { READ },
            allDereferencesToCheck.associateWith { READ },
            onlyPreLabels = true,
          )

        loc.outgoingEdges.toSet().forEach { edge ->
          builder.removeEdge(edge)
          builder.addEdge(edge.withSource(newLoc))
        }

        val positiveLabel = SequenceLabel(newLabels)
        val assumeEdge = XcfaEdge(loc, newLoc, positiveLabel, metadata = EmptyMetaData)
        builder.addEdge(assumeEdge)
        builder.createErrorLoc()
        val errorEdge =
          XcfaEdge(loc, builder.errorLoc.get(), errorLabel!!, metadata = EmptyMetaData)
        builder.addEdge(errorEdge)
      }
    }

    property.transformSpecification(ErrorDetection.ERROR_LOCATION)
    return builder
  }

  private fun getNewLabelsForAccesses(
    vars: VarAccessMap,
    dereferences: DereferenceAccessMap,
    originalLabel: XcfaLabel? = null,
    skipPreLabels: Boolean = false,
    onlyPreLabels: Boolean = false,
  ): Pair<List<XcfaLabel>, StmtLabel?> {
    val varAssertions =
      vars.flatMap { (v, access) ->
        listOf(Eq(v.writeFlag.ref, Int(0))) +
          if (access.isWritten) listOf(Eq(v.readFlag.ref, Int(0))) else listOf()
      }
    val derefAssertions =
      dereferences.flatMap { (deref, access) ->
        listOf(
          Or(
            Neq(deref.array.derefArrayWriteFlag.ref, deref.array),
            Neq(deref.offset.derefOffsetWriteFlag.ref, deref.offset),
          )
        ) +
          if (access.isWritten)
            listOf(
              Or(
                Neq(deref.array.derefArrayReadFlag.ref, deref.array),
                Neq(deref.offset.derefOffsetReadFlag.ref, deref.offset),
              )
            )
          else listOf()
      }
    val assertion =
      (varAssertions + derefAssertions).let { if (it.size == 1) it.first() else And(it) }

    val setLabels = mutableListOf<XcfaLabel>()
    val unsetLabels = mutableListOf<XcfaLabel>()
    vars.forEach { (v, access) ->
      if (access.isWritten) {
        setLabels.add(AssignStmtLabel(v.writeFlag, Int(1)))
        unsetLabels.add(AssignStmtLabel(v.writeFlag, Int(0)))
      }
      if (access.isRead) {
        setLabels.add(AssignStmtLabel(v.readFlag, Int(1)))
        unsetLabels.add(AssignStmtLabel(v.readFlag, Int(0)))
      }
    }
    dereferences.forEach { (deref, access) ->
      if (access.isWritten) {
        setLabels.add(AssignStmtLabel(deref.array.derefArrayWriteFlag, deref.array))
        setLabels.add(AssignStmtLabel(deref.offset.derefOffsetWriteFlag, deref.offset))
        unsetLabels.add(AssignStmtLabel(deref.array.derefArrayWriteFlag, Int(-1)))
        unsetLabels.add(AssignStmtLabel(deref.offset.derefOffsetWriteFlag, Int(-1)))
      }
      if (access.isRead) {
        setLabels.add(AssignStmtLabel(deref.array.derefArrayReadFlag, deref.array))
        setLabels.add(AssignStmtLabel(deref.offset.derefOffsetReadFlag, deref.offset))
        unsetLabels.add(AssignStmtLabel(deref.array.derefArrayReadFlag, Int(-1)))
        unsetLabels.add(AssignStmtLabel(deref.offset.derefOffsetReadFlag, Int(-1)))
      }
    }

    val result = mutableListOf<XcfaLabel>()
    if (!skipPreLabels) {
      result.add(
        SequenceLabel(
          listOf(StmtLabel(AssumeStmt.of(assertion), choiceType = ChoiceType.MAIN_PATH)) + setLabels
        )
      )
    }
    if (!onlyPreLabels) {
      result.add(originalLabel!!)
      result.add(SequenceLabel(unsetLabels))
    }

    val negatedAssertion =
      if (skipPreLabels) null
      else StmtLabel(AssumeStmt.of(Not(assertion)), choiceType = ChoiceType.ALTERNATIVE_PATH)

    return result to negatedAssertion
  }

  private fun replaceEdge(
    builder: XcfaProcedureBuilder,
    location: XcfaLocation,
    edge: XcfaEdge,
    edgeIndex: Int,
    newLabels: List<Pair<List<XcfaLabel>, StmtLabel?>>,
  ) {
    builder.removeEdge(edge)
    var source = location
    newLabels.forEachIndexed { index1, (labels, errorLabel) ->
      if (errorLabel != null) {
        builder.createErrorLoc()
        val errorEdge =
          XcfaEdge(source, builder.errorLoc.get(), errorLabel, metadata = edge.metadata)
        builder.addEdge(errorEdge)
      }

      labels
        .filter { !(it is SequenceLabel && it.labels.isEmpty()) }
        .forEachIndexed { index2, label ->
          val target =
            if (index1 == newLabels.size - 1 && index2 == labels.size - 1) edge.target
            else
              XcfaLocation(
                "${edge.source.name}_dr_${edgeIndex}_${index1}_${index2}",
                metadata = edge.metadata,
              )
          val newEdge = XcfaEdge(source, target, label, metadata = edge.metadata)
          builder.addEdge(newEdge)
          source = target
        }
    }
  }

  private fun removeOriginalErrorEdges(builder: XcfaProcedureBuilder) {
    if (builder.errorLoc.isEmpty) return
    val errorLoc = builder.errorLoc.get()
    val newLoc = XcfaLocation("${errorLoc.name}_reachability", metadata = errorLoc.metadata)
    builder.addLoc(newLoc)
    errorLoc.incomingEdges.toSet().forEach { edge ->
      val newLabel =
        SequenceLabel(
          listOf(
            edge.label,
            StmtLabel(AssumeStmt.of(False())), // abort at original error edges
          )
        )
      builder.removeEdge(edge)
      builder.addEdge(edge.withTarget(newLoc).withLabel(newLabel))
    }
  }

  private fun collectPotentialRacingVars(builder: XcfaProcedureBuilder): Set<VarDecl<*>> {
    val xcfaBuilder = builder.parent
    if (potentialRacingVars == null) {
      potentialRacingVars = getPotentialRacingVars(xcfaBuilder)
      val initProcedure = xcfaBuilder.getInitProcedures().first().first

      val initializeFlags =
        potentialRacingVars!!.flatMap { v ->
          writeFlagVars[v] = Decls.Var("_write_flag_${v.name}", Int())
          readFlagVars[v] = Decls.Var("_read_flag_${v.name}", Int())
          xcfaBuilder.addVar(XcfaGlobalVar(writeFlagVars[v]!!, Int(0), atomic = true))
          xcfaBuilder.addVar(XcfaGlobalVar(readFlagVars[v]!!, Int(0), atomic = true))
          listOf(
            StmtLabel(AssignStmt.of(v.writeFlag, Int(0))),
            StmtLabel(AssignStmt.of(v.readFlag, Int(0))),
          )
        } +
          listOf(
            StmtLabel(AssignStmt.of(derefArrayWriteFlagVar, Int(-1))),
            StmtLabel(AssignStmt.of(derefOffsetWriteFlagVar, Int(-1))),
            StmtLabel(AssignStmt.of(derefArrayReadFlagVar, Int(-1))),
            StmtLabel(AssignStmt.of(derefOffsetReadFlagVar, Int(-1))),
          )
      xcfaBuilder.addVar(XcfaGlobalVar(derefArrayWriteFlagVar, Int(-1), atomic = true))
      xcfaBuilder.addVar(XcfaGlobalVar(derefOffsetWriteFlagVar, Int(-1), atomic = true))
      xcfaBuilder.addVar(XcfaGlobalVar(derefArrayReadFlagVar, Int(-1), atomic = true))
      xcfaBuilder.addVar(XcfaGlobalVar(derefOffsetReadFlagVar, Int(-1), atomic = true))

      val newLoc =
        XcfaLocation("${initProcedure.initLoc.name}_dr", metadata = initProcedure.initLoc.metadata)
      initProcedure.addLoc(newLoc)
      initProcedure.initLoc.outgoingEdges.toSet().forEach { edge ->
        initProcedure.removeEdge(edge)
        initProcedure.addEdge(edge.withSource(newLoc))
      }
      val initEdge =
        XcfaEdge(
          initProcedure.initLoc,
          newLoc,
          SequenceLabel(initializeFlags),
          metadata = EmptyMetaData,
        )
      initProcedure.addEdge(initEdge)
    }

    return potentialRacingVars!!
  }
}
