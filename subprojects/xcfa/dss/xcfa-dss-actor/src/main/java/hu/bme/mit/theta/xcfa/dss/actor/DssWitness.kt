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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.dss.analysis.findBlockRun
import hu.bme.mit.theta.xcfa.dss.analysis.followPath
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * What one block contributes to a witness: the states it reaches at each location ([invariants],
 * null unless known for all its real entry states), its [violations], and the ones it [reported].
 */
data class DssBlockWitness(
  val invariants: Map<XcfaLocation, List<Expr<BoolType>>>?,
  val violations: List<DssViolationRecord>,
  val reported: List<Expr<BoolType>>,
)

/**
 * How a block computed the violation [condition]; [received] are the successors' conditions used.
 */
sealed interface DssViolationRecord {
  val condition: Expr<BoolType>
  val received: List<Pair<String, Expr<BoolType>>>
}

/** A condition over every path of an acyclic block to [targets] (`computeViolationCondition`). */
data class DssAllPathsViolation(
  override val condition: Expr<BoolType>,
  val targets: Map<XcfaLocation, Expr<BoolType>>,
  override val received: List<Pair<String, Expr<BoolType>>>,
) : DssViolationRecord

/** The condition of one counterexample path [edges], ending in the [received] conditions or not. */
data class DssPathViolation(
  override val condition: Expr<BoolType>,
  val edges: List<XcfaEdge>,
  val reachedReceived: Boolean,
  override val received: List<Pair<String, Expr<BoolType>>>,
) : DssViolationRecord

/** DSS's proof: the reached states at every location, or null where they are not known. */
data class DssInvariants(val invariants: Map<XcfaLocation, List<Expr<BoolType>>?>) : Proof

/** Each location's states from every block containing it; null unless all of them know them. */
fun combineInvariants(
  procedure: XcfaProcedure,
  blockGraph: BlockGraph,
  witnesses: Map<String, DssBlockWitness>,
): DssInvariants =
  DssInvariants(
    procedure.locs.associateWith { location ->
      val blocks = blockGraph.blocks.filter { location in it.locations }
      if (blocks.isEmpty()) return@associateWith null
      blocks.flatMap { block ->
        val invariants = witnesses[block.id]?.invariants ?: return@associateWith null
        invariants[location].orEmpty()
      }
    }
  )

/**
 * A path of original edges from the program entry (in state [initial]) to an error: the root's
 * reported condition, followed block by block from the state the previous block ended in.
 */
fun stitchViolationPath(
  blockGraph: BlockGraph,
  witnesses: Map<String, DssBlockWitness>,
  initial: Valuation,
  solver: Solver,
  maxBlocks: Int = 10_000,
): List<XcfaEdge>? {
  val blocksById = blockGraph.blocks.associateBy { it.id }
  val root = blockGraph.root
  return witnesses[root.id]?.reported?.firstNotNullOfOrNull { condition ->
    val path = mutableListOf<XcfaEdge>()
    var block = root
    var current = condition
    var state = initial
    repeat(maxBlocks) {
      val witness = witnesses[block.id] ?: return@firstNotNullOfOrNull null
      val step =
        stepThrough(block, witness, current, state, solver) ?: return@firstNotNullOfOrNull null
      path += step.edges
      val received = step.received ?: return@firstNotNullOfOrNull path
      val (next, nextCondition) =
        received.firstOrNull { (_, c) -> followPath(solver, step.state, emptyList(), c) != null }
          ?: return@firstNotNullOfOrNull null
      block = blocksById[next] ?: return@firstNotNullOfOrNull null
      current = nextCondition
      state = step.state
    }
    null
  }
}

/** One block's part of a stitched path; [received] is null if it ended in the block's own error. */
private class Step(
  val edges: List<XcfaEdge>,
  val state: Valuation,
  val received: List<Pair<String, Expr<BoolType>>>?,
)

private fun stepThrough(
  block: Block,
  witness: DssBlockWitness,
  condition: Expr<BoolType>,
  state: Valuation,
  solver: Solver,
): Step? {
  val allPaths =
    witness.violations.filterIsInstance<DssAllPathsViolation>().lastOrNull {
      it.condition == condition
    }
  if (allPaths != null) {
    val run = findBlockRun(block, allPaths.targets, state, solver) ?: return null
    return Step(run.edges, run.state, allPaths.received.takeUnless { run.end.error })
  }
  // A cyclic block's condition is the disjunction of its path conditions: any one satisfied by
  // the state leads, along its own path, to that path's target.
  return witness.violations.filterIsInstance<DssPathViolation>().firstNotNullOfOrNull { record ->
    val target = if (record.reachedReceived) Or(record.received.map { it.second }) else True()
    followPath(solver, state, record.edges, target)?.let {
      Step(record.edges, it, record.received.takeIf { record.reachedReceived })
    }
  }
}

/** [path] as a trace of [xcfa]'s only process; the states only fix the [initial] values. */
fun violationTrace(
  xcfa: XCFA,
  path: List<XcfaEdge>,
  initial: Valuation,
): Trace<XcfaState<PtrState<*>>, XcfaAction> {
  val start: XcfaState<PtrState<*>> =
    XcfaState(xcfa, path.first().source, PtrState(ExplState.of(initial)))
  val states = path.map { XcfaState<PtrState<*>>(xcfa, it.target, PtrState(ExplState.top())) }
  return Trace.of(listOf(start) + states, path.map { XcfaAction(0, it) })
}
