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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredAbstractors
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/** How [packTreePostcondition] abstracts an exit node's exact path onto the predicates. */
enum class DssTreeAbstraction {
  /** Each predicate or its negation, if the path implies it: two queries per predicate. */
  CARTESIAN,
  /**
   * Every combination of the predicates the path allows, as a disjunction of cubes (CPAchecker's
   * Boolean predicate abstraction): one query per cube, so up to exponentially many.
   */
  BOOLEAN,
}

/**
 * A postcondition at [location] read off the paths of a CEGAR checker's reachability tree
 * ([LocationInvariants.tree]) instead of its abstract states: CPAchecker's block abstraction, which
 * abstracts once at the block's end rather than at every location.
 *
 * For every uncovered exit node, the path to it from its nearest ancestor that covers some node (or
 * from the root) is taken exactly, starting from that ancestor's abstract state, and the result is
 * abstracted onto [predicates] as [abstraction] says.
 *
 * Sound: a node that covers no other node is reached only along its tree edge, so the concrete
 * states of an exit node lie within its anchor's state followed by the path. Each exit node's part
 * also implies the node's own abstract state, so the result is never weaker than
 * [packPostcondition]'s.
 *
 * With [exactExits], every exit node counts, also one covered by another, and each starts its path
 * from its nearest *proper* covering ancestor: an exit node that covers others keeps its own exact
 * path instead of its abstract state, so paths meeting at the exit are not abstracted there. Also
 * sound: the states a covered exit node stands for are counted by its own part, and states that
 * continue from a covering exit node are anchored at it by its descendants.
 *
 * Returns null when the proof has no tree (a bounded checker) or the tree has several processes;
 * the caller then packs the plain postcondition.
 */
fun packTreePostcondition(
  proof: LocationInvariants,
  location: XcfaLocation,
  predicates: Set<Expr<BoolType>>,
  solverFactory: SolverFactory,
  exactExits: Boolean = false,
  abstraction: DssTreeAbstraction = DssTreeAbstraction.CARTESIAN,
): Expr<BoolType>? {
  val nodes = proof.tree?.nodes ?: return null
  // A node past the final location has no process left; one with several is not a block's tree
  if (nodes.any { xcfaState(it).processes.size > 1 }) return null
  val exits =
    nodes.filter { node ->
      (exactExits || !node.isCovered) &&
        !xcfaState(node).bottom &&
        process(node)?.locs?.peek() == location
    }
  if (exits.isEmpty()) return False()
  val solver = withSolverConstructionLock { solverFactory.createSolver() }
  try {
    return Or(exits.mapNotNull { exitPart(solver, it, predicates, exactExits, abstraction) })
  } finally {
    runCatching { solver.close() }
  }
}

/** The abstraction of [exit]'s path from its anchor, or null if that path is infeasible. */
private fun exitPart(
  solver: Solver,
  exit: ArgNode<*, *>,
  predicates: Set<Expr<BoolType>>,
  exactExits: Boolean,
  abstraction: DssTreeAbstraction,
): Expr<BoolType>? {
  val path = ArrayDeque<XcfaAction>()
  var anchor = exit
  // With exactExits, the exit node itself never anchors, even if it covers others
  var ownStep = exactExits
  while (ownStep || anchor.coveredNodes.findAny().isEmpty) {
    ownStep = false
    val edge = anchor.inEdge.orElse(null) ?: break
    path.addFirst(edge.action as XcfaAction)
    anchor = edge.source
  }
  val toChecker = renaming(process(exit)!!)
  val toProgram = toChecker.reverseMapping()
  var indexing: VarIndexing = VarIndexingFactory.indexing(0)
  WithPushPop(solver).use {
    solver.add(PathUtils.unfold(stateExpr(anchor), indexing))
    for (action in path) {
      solver.add(PathUtils.unfold(action.toExpr(), indexing))
      indexing = indexing.add(action.nextIndexing())
    }
    if (solver.check().isUnsat) return null
    val own = ExprUtils.changeDecls(stateExpr(exit), toProgram)
    if (abstraction == DssTreeAbstraction.BOOLEAN) {
      // The path is already on the solver: the abstractor only enumerates the cubes over it
      val inChecker = PredPrec.of(predicates.map { ExprUtils.changeDecls(it, toChecker) })
      val cubes =
        PredAbstractors.booleanSplitAbstractor(solver)
          .createStatesForExpr(True(), indexing, inChecker, indexing)
          .map { ExprUtils.changeDecls(it.toExpr(), toProgram) }
      val cover = Or(cubes)
      // Own atoms outside the predicates cannot be implied by the cubes
      val implied = predicates.containsAll(ExprUtils.getAtoms(own))
      return if (implied) cover else And(cover, own)
    }
    val literals =
      predicates.mapNotNull { predicate ->
        val atEnd = PathUtils.unfold(ExprUtils.changeDecls(predicate, toChecker), indexing)
        when {
          unsatWith(solver, Not(atEnd)) -> predicate
          unsatWith(solver, atEnd) -> Not(predicate)
          else -> null
        }
      }
    val ownLiterals = if (own is AndExpr) own.ops.toSet() else setOf(own)
    return if (literals.containsAll(ownLiterals)) And(literals) else And(literals + own)
  }
}

private fun unsatWith(solver: Solver, expr: Expr<BoolType>): Boolean =
  WithPushPop(solver).use {
    solver.add(expr)
    solver.check().isUnsat
  }

private fun xcfaState(node: ArgNode<*, *>) = node.state as XcfaState<*>

private fun process(node: ArgNode<*, *>): XcfaProcessState? =
  xcfaState(node).processes.values.singleOrNull()

private fun stateExpr(node: ArgNode<*, *>): Expr<BoolType> =
  ((xcfaState(node).sGlobal as PtrState<*>).innerState as ExprState).toExpr()

/** The program's variables to the process's own instances of them. */
private fun renaming(process: XcfaProcessState): Map<VarDecl<*>, VarDecl<*>> =
  if (process.varLookup.isEmpty()) emptyMap()
  else process.varLookup.reversed().reduce { a, b -> a + b }
