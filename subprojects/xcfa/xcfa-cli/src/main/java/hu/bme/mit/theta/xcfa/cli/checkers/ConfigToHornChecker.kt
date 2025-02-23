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
package hu.bme.mit.theta.xcfa.cli.checkers

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.chc.CexTree
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker
import hu.bme.mit.theta.analysis.algorithm.chc.Invariant
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.functype.FuncAppExpr
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.ProofNode
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.HornConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa2chc.toCHC
import kotlin.jvm.optionals.getOrNull

fun getHornChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

  checkState(xcfa.isInlined, "Only inlined XCFAs work right now")
  checkState(xcfa.initProcedures.size == 1, "Only one-procedure XCFAs work right now")

  val hornConfig = config.backendConfig.specConfig as HornConfig

  val property = config.inputConfig.property

  val checker =
    HornChecker(
      relations = xcfa.initProcedures[0].first.toCHC(property == ErrorDetection.TERMINATION),
      hornSolverFactory = getSolver(hornConfig.solver, hornConfig.validateSolver),
      logger = logger,
    )

  return SafetyChecker<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
    val result = checker.check(null)

    if (result.isSafe) {
      SafetyResult.safe(EmptyProof.getInstance())
    } else if (result.isUnsafe) {
      try {
        getProperTrace(xcfa, result)
      } catch (t: Throwable) {
        SafetyResult.unsafe(
          Trace.of(
            listOf(
              XcfaState(
                xcfa,
                xcfa.initProcedures.get(0).first.errorLoc.getOrNull()
                  ?: XcfaLocation("<missing!>", metadata = EmptyMetaData),
                PtrState(PredState.of(True())),
              )
            ),
            listOf(),
          ),
          EmptyProof.getInstance(),
        )
      }
    } else {
      SafetyResult.unknown()
    }
  }
}

private fun getProperTrace(
  xcfa: XCFA,
  result: SafetyResult<Invariant, CexTree>,
): SafetyResult.Unsafe<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>>? {
  val getName = { s: String ->
    val split = s.split("_")
    val allButLast = split.subList(0, split.size - 1)
    allButLast.joinToString("_")
  }
  val loc = { proofNode: ProofNode ->
    if (proofNode.expr is FuncAppExpr<*, *>) {
      var func: Expr<*> = proofNode.expr
      while (func is FuncAppExpr<*, *>) {
        func = func.func
      }
      func as RefExpr<*>
      val locs = xcfa.procedures.flatMap { it.locs }
      locs.firstOrNull { it.name == getName(func.decl.name) }
        ?: locs.firstOrNull { it.name == func.decl.name }
    } else null
  }
  val states = mutableListOf<XcfaState<PtrState<*>>>()
  val actions = mutableListOf<XcfaAction>()
  var proofNode: ProofNode? = result.asUnsafe().cex.proofNode
  var lastLoc: XcfaLocation? = null
  while (proofNode != null) {
    loc(proofNode)?.also { currentLoc ->
      if (lastLoc == null) {
        states.add(XcfaState(xcfa, currentLoc, PtrState(PredState.of())))
      } else {
        val edge = currentLoc.outgoingEdges.firstOrNull { it.target == lastLoc }
        if (edge != null) {
          states.add(XcfaState(xcfa, currentLoc, PtrState(PredState.of())))
          actions.add(XcfaAction(0, edge))
        } else {
          // z3 is messing with us, we need to find out what trace it optimized out.
          val (length, edges) = getShortestPath(currentLoc, lastLoc!!)
          checkState(length < Int.MAX_VALUE)
          lateinit var loc: XcfaLocation
          for (xcfaEdge in edges.reversed()) {
            loc = xcfaEdge.source
            states.add(XcfaState(xcfa, loc, PtrState(PredState.of())))
            actions.add(XcfaAction(0, xcfaEdge))
          }
          checkState(loc == currentLoc)
        }
      }
      lastLoc = currentLoc
    }
    proofNode = proofNode.children.getOrNull(0)
  }
  if (lastLoc != xcfa.initProcedures[0].first.initLoc) {
    val (length, edges) = getShortestPath(xcfa.initProcedures[0].first.initLoc, lastLoc!!)
    checkState(length < Int.MAX_VALUE)
    lateinit var loc: XcfaLocation
    for (xcfaEdge in edges.reversed()) {
      loc = xcfaEdge.source
      states.add(XcfaState(xcfa, loc, PtrState(PredState.of())))
      actions.add(XcfaAction(0, xcfaEdge))
    }
    checkState(loc == xcfa.initProcedures[0].first.initLoc)
  }

  return SafetyResult.unsafe(
    Trace.of(states.reversed(), actions.reversed()),
    EmptyProof.getInstance(),
  )
}

fun getShortestPath(start: XcfaLocation, end: XcfaLocation): Pair<Int, List<XcfaEdge>> {
  val visited = mutableSetOf(start)
  val waitlist = mutableListOf(Pair(start, listOf<XcfaEdge>()))
  while (waitlist.isNotEmpty()) {
    val (loc, edges) = waitlist.removeFirst()
    for (outgoingEdge in loc.outgoingEdges) {
      if (outgoingEdge.target == end) {
        return Pair(edges.size + 1, edges + outgoingEdge)
      } else if (visited.contains(outgoingEdge.target)) {
        // do nothing
      } else {
        visited.add(outgoingEdge.target)
        waitlist.add(Pair(outgoingEdge.target, edges + outgoingEdge))
      }
    }
  }
  return Pair(Int.MAX_VALUE, emptyList())
}
