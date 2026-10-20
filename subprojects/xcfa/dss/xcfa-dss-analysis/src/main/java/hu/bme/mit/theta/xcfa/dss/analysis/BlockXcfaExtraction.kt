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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import java.util.Optional

data class BlockXcfaExtraction(
  val xcfa: XCFA,
  val locationMapping: Map<XcfaLocation, XcfaLocation>,
  val entryLocation: XcfaLocation,
  val exitLocation: XcfaLocation,
  val preconditionEdge: XcfaEdge? = null,
  val violationConditionEdge: XcfaEdge? = null,
  val originalLocations: Map<XcfaLocation, XcfaLocation> = emptyMap(),
  val originalEdges: Map<XcfaEdge, XcfaEdge> = emptyMap(),
)

/**
 * [block] as a standalone [XCFA], with [precondition] at the entry and [violationCondition] at the
 * exit.
 */
fun extractBlockXcfa(
  sourceProcedure: XcfaProcedure,
  block: Block,
  globalVars: Set<XcfaGlobalVar> = emptySet(),
  precondition: Expr<BoolType>? = null,
  violationCondition: Expr<BoolType>? = null,
  keepSpecificationTargets: Boolean = true,
): BlockXcfaExtraction {
  val name = "${sourceProcedure.name}__${block.id}"

  fun cloneOf(original: XcfaLocation, nameSuffix: String = "") =
    XcfaLocation(
      original.name + nameSuffix,
      original.initial,
      original.final,
      original.error && keepSpecificationTargets,
      original.metadata,
    )

  val clonedLocations: Map<XcfaLocation, XcfaLocation> = block.locations.associateWith(::cloneOf)
  // Split loop head (CPAchecker's INITIAL vs. FINAL): one analysis covers one iteration
  val splitEntry = block.initialLocation == block.finalLocation
  val blockEntry =
    if (splitEntry) cloneOf(block.initialLocation, "__entry")
    else clonedLocations.getValue(block.initialLocation)

  val allLocations = clonedLocations.values.toMutableSet().apply { add(blockEntry) }
  val clonedEdges = mutableSetOf<XcfaEdge>()
  val originalEdges = mutableMapOf<XcfaEdge, XcfaEdge>()
  fun connect(source: XcfaLocation, target: XcfaLocation, edge: XcfaEdge) {
    source.outgoingEdges.add(edge)
    target.incomingEdges.add(edge)
    clonedEdges.add(edge)
  }

  for (original in block.edges) {
    val source =
      if (splitEntry && original.source == block.initialLocation) blockEntry
      else clonedLocations.getValue(original.source)
    val target = clonedLocations.getValue(original.target)
    val clone = XcfaEdge(source, target, original.label, original.metadata)
    connect(source, target, clone)
    originalEdges[clone] = original
  }

  val exitLocation = clonedLocations.getValue(block.finalLocation)
  val procedureVars = sourceProcedure.vars.toMutableSet()

  var errorLocation = allLocations.firstOrNull { it.error }
  var violationConditionEdge: XcfaEdge? = null
  if (violationCondition != null) {
    val target =
      errorLocation
        ?: XcfaLocation("${name}__vcond", error = true, metadata = EmptyMetaData).also {
          allLocations.add(it)
          errorLocation = it
        }
    val auxVars = DssAuxVars.collectVars(violationCondition)
    procedureVars.addAll(auxVars)
    val label =
      SequenceLabel(auxVars.map { StmtLabel(Havoc(it)) } + StmtLabel(Assume(violationCondition)))
    violationConditionEdge = XcfaEdge(exitLocation, target, label, EmptyMetaData)
    connect(exitLocation, target, violationConditionEdge)
  }

  var entryLoc = blockEntry
  var preconditionEdge: XcfaEdge? = null
  if (precondition != null) {
    val syntheticEntry = XcfaLocation("${name}__pre", metadata = EmptyMetaData)
    preconditionEdge =
      XcfaEdge(syntheticEntry, entryLoc, StmtLabel(Assume(precondition)), EmptyMetaData)
    connect(syntheticEntry, entryLoc, preconditionEdge)
    allLocations.add(syntheticEntry)
    entryLoc = syntheticEntry
  }

  val blockProcedure =
    XcfaProcedure(
      name = name,
      params = emptyList(),
      vars = procedureVars,
      locs = allLocations,
      edges = clonedEdges,
      initLoc = entryLoc,
      finalLoc = Optional.ofNullable(clonedLocations.values.firstOrNull { it.final }),
      errorLoc = Optional.ofNullable(errorLocation),
    )
  // The public constructor would re-run the pass pipeline on builders
  val xcfa =
    XCFA(name, globalVars).recreate(setOf(blockProcedure), listOf(blockProcedure to emptyList()))
  return BlockXcfaExtraction(
    xcfa,
    clonedLocations,
    blockEntry,
    exitLocation,
    preconditionEdge,
    violationConditionEdge,
    clonedLocations.entries.associate { (original, clone) -> clone to original } +
      (blockEntry to block.initialLocation),
    originalEdges,
  )
}
