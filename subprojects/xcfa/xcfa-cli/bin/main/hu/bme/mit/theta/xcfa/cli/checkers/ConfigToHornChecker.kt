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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.functype.FuncAppExpr
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.ProofNode
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.HornConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
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

  val property = config.inputConfig.property.verifiedProperty

  val xcfa =
    xcfa.optimizeFurther(
      ProcedurePassManager(
        listOf(NoUninitVar(), HavocToUninitVar(), NoParallelEdgesPass(), EliminateSelfLoops())
      )
    )

  val (vars, chc) =
    xcfa.initProcedures[0]
      .first
      .toCHC(property == ErrorDetection.TERMINATION, hornConfig.rankingFuncConstr)

  val checker =
    HornChecker(
      relations = chc,
      hornSolverFactory = getSolver(hornConfig.solver, hornConfig.validateSolver),
      logger = logger,
    )

  return SafetyChecker<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
    val result = checker.check(null)

    if (result.isSafe) {
      //      if (property == ErrorDetection.TERMINATION) {
      //        val invariant = result.asSafe().proof
      //        val finalFunc = invariant.lookup.keys.first { it.name.contains("_final") }.constDecl
      //        val params = vars.map { Param(it.name, it.type).ref }.toList()
      //        val noRankFunc = params.filter { it.decl.name != "__ranking_function" }
      //        val rankFunc = params.filter { it.decl.name == "__ranking_function" }.first()
      //        val lhs = App(finalFunc.ref as Expr<FuncType<in Type, BoolType>>, params)
      //        val f = Const("f", funcType(noRankFunc.map { it.type }, rankFunc.type))
      //        val rhs = Eq(App(f.ref as Expr<FuncType<in Type, Type>>, noRankFunc), rankFunc)
      //        val solver = Z3SolverFactory.getInstance().createSolver()
      //        WithPushPop(solver).use {
      //          solver.add(Eq(lhs, rhs))
      //          val status = solver.check()
      //          check(status.isSat)
      //          val model = solver.model
      //          System.err.println(model.toMap()[f])
      //        }
      //      }
      SafetyResult.safe(EmptyProof.getInstance())
    } else if (result.isUnsafe) {
      try {
        getProperTrace(xcfa, result, vars)
      } catch (t: Throwable) {
        logger.writeln(Logger.Level.INFO, "Could not get proper trace: ${t.stackTraceToString()}\n")
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
  vars: List<VarDecl<*>>,
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
  val toState = { proofNode: ProofNode ->
    if (proofNode.expr is FuncAppExpr<*, *>) {
      var f: Expr<*> = proofNode.expr
      val values = mutableMapOf<Decl<*>, LitExpr<*>>()
      var i = vars.size - 1
      while (f is FuncAppExpr<*, *>) {
        values[vars[i--]] = f.param.eval(ImmutableValuation.empty())
        f = f.func
      }
      ExplState.of(ImmutableValuation.from(values))
    } else ExplState.top()
  }
  val states = mutableListOf<XcfaState<PtrState<*>>>()
  val actions = mutableListOf<XcfaAction>()
  var proofNode: ProofNode? = result.asUnsafe().cex.proofNode
  var lastLoc: XcfaLocation? = null
  while (proofNode != null) {
    loc(proofNode)?.also { currentLoc ->
      if (lastLoc == null) {
        states.add(XcfaState(xcfa, currentLoc, PtrState(toState(proofNode as ProofNode))))
      } else {
        val edges = currentLoc.outgoingEdges.filter { it.target == lastLoc }
        if (edges.isNotEmpty()) {
          states.add(XcfaState(xcfa, currentLoc, PtrState(toState(proofNode as ProofNode))))
          val action =
            if (edges.size == 1) {
              XcfaAction(0, edges.first())
            } else {
              XcfaAction(
                0,
                currentLoc,
                lastLoc!!,
                NondetLabel(edges.map(XcfaEdge::label).toSet()),
                edges.fold(EmptyMetaData as MetaData) { e1, e2 -> e1.combine(e2.metadata) },
              )
            }
          actions.add(action)
        } else {
          // z3 is messing with us, we need to find out what trace it optimized out.
          val (length, edges) = getShortestPath(currentLoc, lastLoc!!)
          checkState(length < Int.MAX_VALUE)
          lateinit var loc: XcfaLocation
          // TODO collect parallel edges into nondet label?
          for (xcfaEdge in edges.reversed()) {
            loc = xcfaEdge.source
            states.add(XcfaState(xcfa, loc, PtrState(toState(proofNode as ProofNode))))
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
      states.add(XcfaState(xcfa, loc, PtrState(ExplState.top())))
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
