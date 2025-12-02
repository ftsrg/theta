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
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.chc.CexTree
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker
import hu.bme.mit.theta.analysis.algorithm.chc.Invariant
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.functype.FuncAppExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
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
import kotlin.collections.plus
import kotlin.jvm.optionals.getOrNull

fun getHornChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
  parseContext: ParseContext,
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

  val hornChecker = { chc: List<Relation> ->
    HornChecker(
      relations = chc,
      hornSolverFactory = getSolver(hornConfig.solver, hornConfig.validateSolver),
      logger = logger,
    )
  }

  try {
    if (parseContext.multiThreading) {
      error("Current CHC encoding does not support multithreading")
    }
    val (vars, chc) =
      xcfa.initProcedures[0]
        .first
        .toCHC(property == ErrorDetection.TERMINATION, hornConfig.rankingFuncConstr)
    val checker = hornChecker(chc)

    return SafetyChecker<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
      val result = checker.check(null)

      if (result.isSafe) {
        SafetyResult.safe(EmptyProof.getInstance())
      } else if (result.isUnsafe) {
        try {
          getProperTrace(xcfa, result as SafetyResult<Invariant, CexTree>, vars)
        } catch (t: Throwable) {
          logger.writeln(
            Logger.Level.INFO,
            "Could not get proper trace: ${t.stackTraceToString()}\n",
          )
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
  } catch (t: Throwable) {
    logger.benchmark(
      "Error initializing XCFA procedure as CHC, falling back to monolithic (due to %s)",
      t.message,
    )

    return getPipelineChecker(
      config,
      xcfa,
      parseContext,
      { monolithicExpr ->
        val vars = monolithicExpr.vars
        val types = vars.map { it.type }.toTypedArray()
        val oldParams = vars.associateWith { Param("|" + it.name + "|", it.type) }
        val oldParamList = vars.map { oldParams[it]!!.ref }.toTypedArray()
        val newParams = vars.associateWith { Param("|" + it.name + "_new|", it.type) }
        val inv = Relation("inv", *types)

        inv(*oldParamList) += ExprUtils.changeDecls(monolithicExpr.initExpr, oldParams)

        !(inv(*oldParamList) with Not(ExprUtils.changeDecls(monolithicExpr.propExpr, oldParams)))

        val expr = PathUtils.unfold(monolithicExpr.transExpr, VarIndexingFactory.indexing(0))
        // var[0] is oldParam, var[-1]is newParam, everything else is a fresh param
        var cnt = 0
        val consts =
          ExprUtils.getIndexedConstants(expr).associateWith {
            if (it.index == 0) oldParams[it.varDecl]!!
            else if (it.index == monolithicExpr.transOffsetIndex[it.varDecl])
              newParams[it.varDecl]!!
            else Param("__tmp_${cnt++}", it.type)
          }
        val newParamList =
          vars
            .map {
              if (monolithicExpr.transOffsetIndex[it] == 0) oldParams[it]!!.ref
              else newParams[it]!!.ref
            }
            .toTypedArray()
        val paramdExpr = ExprUtils.changeDecls(expr, consts)
        inv(*newParamList) += inv(*oldParamList).expr + paramdExpr

        SafetyChecker<PredState, Trace<ExplState, ExprAction>, UnitPrec> { prec ->
          val result = hornChecker(listOf(inv)).check(null)
          if (result.isSafe) {
            SafetyResult.safe(PredState.of())
          } else if (result.isUnsafe) {
            var proofNode: ProofNode? = result.asUnsafe().cex.proofNode
            val states = mutableListOf<ExplState>()
            while (proofNode != null) {
              val state =
                if (proofNode.expr is FuncAppExpr<*, *>) {
                  var f: Expr<*> = proofNode.expr
                  val values = mutableMapOf<Decl<*>, LitExpr<*>>()
                  var i = vars.size - 1
                  while (f is FuncAppExpr<*, *>) {
                    values[vars[i--]] = f.param.eval(ImmutableValuation.empty())
                    f = f.func
                  }
                  ExplState.of(ImmutableValuation.from(values))
                } else if (proofNode.expr is FalseExpr) {
                  null
                } else if (proofNode.expr is TrueExpr) {
                  // init expr?
                  null
                } else ExplState.top()
              if (state != null) states.add(state)
              proofNode = proofNode.children.getOrNull(0)
            }
            SafetyResult.unsafe(
              Trace.of(states.reversed(), (1 until states.size).map { monolithicExpr.action() }),
              PredState.of(),
            )
          } else {
            SafetyResult.unknown()
          }
        }
      },
      logger,
    )
      as SafetyChecker<EmptyProof, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>>
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
