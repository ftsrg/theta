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
import hu.bme.mit.theta.xcfa.dss.decomposition.GhostEdgeMetadata
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import java.util.Optional

/**
 * The result of [extractBlockXcfa]: the standalone [xcfa], plus [locationMapping] from the original
 * [Block]'s locations to their clones inside [xcfa] (the clones do not share identity with the
 * source procedure). [exitLocation] is the clone where the block's postcondition is read off
 * (CPAchecker's block-end abstraction point). It differs from
 * `locationMapping[block.initialLocation]` even when the block starts and ends at the same location
 * (a loop body), see [extractBlockXcfa]. [preconditionEdge] and [violationConditionEdge] are the
 * synthetic edges added for the precondition and the violation condition, if any.
 */
data class BlockXcfaExtraction(
  val xcfa: XCFA,
  val locationMapping: Map<XcfaLocation, XcfaLocation>,
  val entryLocation: XcfaLocation,
  val exitLocation: XcfaLocation,
  val preconditionEdge: XcfaEdge? = null,
  val violationConditionEdge: XcfaEdge? = null,
)

/**
 * Extracts [block] into a standalone, checkable [XCFA] that contains only the block's own locations
 * and edges. This is the Theta counterpart of what CPAchecker's `BlockCPA` does inside one shared
 * CFA: restricting the analysis to the block's edges, starting it at the block entry, and making
 * the violation-condition location a target when violation conditions are attached.
 * - [precondition] (CPAchecker: the start state of a block analysis) becomes a synthetic
 *   `assume(precondition)` edge in front of the block entry. `null` means the most general entry
 *   state (top), which starts the analysis without any constraint.
 * - [violationCondition] (CPAchecker: the violation conditions attached to the `BlockState`, which
 *   make the violation-condition location a target) becomes an edge from [exitLocation] into an
 *   error location that havocs the auxiliary existential variables of the condition (see
 *   [DssAuxVars]) and then assumes it. Reaching the error location through that edge is exactly
 *   "reaching the block end in a state that satisfies the violation condition".
 * - [keepSpecificationTargets] decides whether the block's own error locations stay error
 *   locations. CPAchecker always checks the specification; Theta's checkers stop at the first
 *   counterexample, so the block analysis turns them off when it only wants the postcondition of a
 *   block whose targets are already known to be reachable (see `PredicateBlockBehavior`).
 *
 * The block entry and the block exit get separate clones when they are the same location (a loop
 * body that starts and ends at the loop head). This mirrors CPAchecker's `BlockStateType.INITIAL`
 * vs. `FINAL`: the block end "cannot be reached directly before processing the first edge" -
 * without the split, the entry state would immediately count as a block-end state, and the body
 * could be iterated arbitrarily often inside a single block analysis.
 *
 * Every [XcfaLocation]/[XcfaEdge] is cloned rather than reused: a location's
 * `incomingEdges`/`outgoingEdges` are mutable sets that still contain every edge of the whole
 * source procedure, so reusing them would not isolate the block. [sourceProcedure] supplies `vars`
 * (unfiltered), and [globalVars] the global variables of the extracted program (DSS passes the
 * program's real globals only for the root block, whose entry is the real program entry).
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
  val splitEntry = block.initialLocation == block.finalLocation
  val blockEntry =
    if (splitEntry) cloneOf(block.initialLocation, "__entry")
    else clonedLocations.getValue(block.initialLocation)

  val allLocations = clonedLocations.values.toMutableSet().apply { add(blockEntry) }
  val clonedEdges = mutableSetOf<XcfaEdge>()
  fun connect(source: XcfaLocation, target: XcfaLocation, edge: XcfaEdge) {
    source.outgoingEdges.add(edge)
    target.incomingEdges.add(edge)
    clonedEdges.add(edge)
  }

  for (original in block.edges) {
    // In a split loop-head block, the body leaves from the entry clone; the ghost edge (if any)
    // leaves from the exit clone, i.e., only after the body has been processed.
    val source =
      if (
        splitEntry &&
          original.source == block.initialLocation &&
          original.metadata != GhostEdgeMetadata
      )
        blockEntry
      else clonedLocations.getValue(original.source)
    val target = clonedLocations.getValue(original.target)
    connect(source, target, XcfaEdge(source, target, original.label, original.metadata))
  }

  val exitLocation = clonedLocations.getValue(block.violationConditionLocation)
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
    val auxVars = DssAuxVars.varsOf(violationCondition)
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
  // XCFA's public constructor only accepts XcfaProcedureBuilders, which would re-run the whole
  // pass/optimize pipeline - build an empty container instead and swap in the already-built
  // procedure via `recreate`.
  val xcfa =
    XCFA(name, globalVars).recreate(setOf(blockProcedure), listOf(blockProcedure to emptyList()))
  return BlockXcfaExtraction(
    xcfa,
    clonedLocations,
    blockEntry,
    exitLocation,
    preconditionEdge,
    violationConditionEdge,
  )
}
