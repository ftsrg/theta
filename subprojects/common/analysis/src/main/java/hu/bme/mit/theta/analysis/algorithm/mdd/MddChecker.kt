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
package hu.bme.mit.theta.analysis.algorithm.mdd

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.*
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.*
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.LitExprConverter
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddApproximation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.SymbolicKeys
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddProof
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.TraceSearch
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.generateTrace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.collection.CollectionUtil
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool

class MddChecker
@JvmOverloads
constructor(
  private val monolithicExpr: MonolithicExpr,
  private val solverPool: SolverPool,
  private val logger: Logger,
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  private val traceTimeout: Long = 10,
  private val variableOrdering: List<VarDecl<*>> = monolithicExpr.orderVars(),
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
  private val solverMeasurements: Boolean = false,
  private val traceSearch: TraceSearch = TraceSearch.DFS,
  private val approximation: MddApproximation = MddApproximation.exact(),
  // keys may be terms over symbolic values, and state terminals hold their path condition
  private val symbolicValues: Boolean = false,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val outer = LitExprConverter.isSymbolic()
    LitExprConverter.setSymbolic(symbolicValues)
    try {
      return checkWithKeys()
    } finally {
      LitExprConverter.setSymbolic(outer)
    }
  }

  private fun checkWithKeys(): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()

    // variable-level look-ahead bounds keys by value, which interned keys are not
    val lookAheadStrategy =
      if (
        symbolicValues &&
          lookAheadStrategy == MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL
      )
        MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL
      else lookAheadStrategy
    val mddGraph =
      JavaMddFactory.getDefault()
        .createMddGraph(
          if (symbolicValues) ExprLatticeDefinition.forSymbolicExpr(solverPool)
          else ExprLatticeDefinition.forExpr()
        )
    val mddGraph2 = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
    mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    mddGraph2.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    mddGraph.setAttribute(MddExpressionRepresentation.APPROXIMATION, approximation)
    mddGraph2.setAttribute(MddExpressionRepresentation.APPROXIMATION, approximation)

    val stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph)
    val transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph2)

    variableOrdering.forEach {
      Preconditions.checkArgument(
        monolithicExpr.vars.contains(it),
        "Variable ordering contains variable not present in vars List",
      )
    }

    Preconditions.checkArgument(
      variableOrdering.size == CollectionUtil.createSet(variableOrdering).size,
      "Variable ordering contains duplicates",
    )
    val identityExprs = mutableListOf<Expr<BoolType>>()
    for (v in variableOrdering.reversed()) {
      var domainSize: Int // = max(v.type.domainSize.finiteSize.toInt().toDouble(), 0.0).toInt()

      //     if (domainSize > 100) {
      domainSize = 0

      //     }
      stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))

      val index = monolithicExpr.transOffsetIndex[v]
      if (index > 0) {
        transOrder.createOnTop(
          MddVariableDescriptor.create(
            v.getConstDecl(monolithicExpr.transOffsetIndex[v]),
            domainSize,
          )
        )
      } else {
        transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), domainSize))
        identityExprs.add(Eq(v.getConstDecl(0).ref, v.getConstDecl(1).ref))
      }

      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))
    }

    val stateSig = stateOrder.defaultSetSignature
    val transSig = transOrder.defaultSetSignature

    if (symbolicValues) {
      SymbolicKeys.setLevels(
        variableOrdering
          .flatMap {
            listOf(
              it.getConstDecl(0),
              it.getConstDecl(maxOf(monolithicExpr.transOffsetIndex[it], 1)),
            )
          }
          .toSet(),
        solverPool,
      )
    }

    val solverCountBefore = solverPool.checkCount
    val ssgTime = Stopwatch.createStarted()

    val initExpr = PathUtils.unfold(monolithicExpr.initExpr, 0)
    val initNode =
      if (symbolicValues) symbolicInit(initExpr, stateSig, transSig)
      else
        stateSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.of(initExpr, { it as Decl<*> }, solverPool)
        )

    logger.write(Logger.Level.INFO, "Created initial node\n")

    val transNodes = mutableListOf<MddHandle>()
    val descriptors = mutableListOf<AbstractNextStateDescriptor>()
    for (expr in monolithicExpr.split) {
      val transExpr =
        And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(identityExprs))
      val transitionNode =
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.of(transExpr, { it as Decl<*> }, solverPool, true)
        )
      transNodes.add(transitionNode)
      descriptors.add(MddNodeNextStateDescriptor.of(transitionNode))
    }
    val nextStates: AbstractNextStateDescriptor = OrNextStateDescriptor.create(descriptors)

    val negatedPropExpr = PathUtils.unfold(Not(monolithicExpr.propExpr), 0)
    val propNode =
      stateSig.topVariableHandle.checkInNode(
        MddExpressionTemplate.of(negatedPropExpr, { it as Decl<*> }, solverPool)
      )
    val targetedNextStates =
      if (monolithicExpr.propExpr == True()) nextStates
      else OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode)

    logger.write(Logger.Level.INFO, "Created next-state node, starting fixed point calculation\n")
    val stateSpaceProvider = iterationStrategy.createProvider(stateSig.variableOrder)

    val stateSpace =
      stateSpaceProvider.compute(
        MddNodePostcondition.of(initNode),
        targetedNextStates,
        stateSig.topVariableHandle,
      )

    ssgTime.stop()

    val solverCheckCount = solverPool.checkCount - solverCountBefore
    logger.write(Logger.Level.INFO, "Solver check() calls: $solverCheckCount\n")

    totalTime.stop()

    val propViolating = stateSpace.intersection(propNode)

    logger.write(Logger.Level.INFO, "Calculated violating states\n")

    val violatingSize = MddInterpreter.calculateNonzeroCount(propViolating)
    logger.write(Logger.Level.INFO, "States violating the property: $violatingSize\n")

    val stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace)
    logger.write(Logger.Level.DETAIL, "State space size: $stateSpaceSize\n")

    val statistics =
      MddAnalysisStatistics(
        violatingSize,
        stateSpaceSize,
        stateSpaceProvider.hitCount,
        stateSpaceProvider.queryCount,
        stateSpaceProvider.cacheSize,
        ssgTime.elapsedMillis(),
        totalTime.elapsedMillis(),
      )

    logger.write(Logger.Level.MAINSTEP, "%s\n", statistics)

    if (solverMeasurements) {
      stateSpaceProvider.clear()
      structuralRerun(transNodes, transSig, initNode, stateSig, ssgTime.elapsedMillis())
    }

    if (violatingSize == 0L && approximation.isUnderApproximated) {
      logger.write(Logger.Level.RESULT, "Cannot justify the verdict under %s\n", approximation)
      return SafetyResult.unknown(statistics)
    }

    // the invariant decodes keys, which in symbolic mode only works while this run's keys are on
    val proof =
      MddProof.of(stateSpace, proofStrategy).also { if (symbolicValues) it.getInvariant() }
    val result: SafetyResult<MddProof, Trace<ExplState, ExprAction>>
    if (violatingSize != 0L) {
      // on trace generation timeout, fall back to an empty trace
      val trace =
        generateTrace(
          transNodes,
          transSig,
          stateSpace,
          propViolating,
          initNode,
          stateSig,
          monolithicExpr,
          traceTimeout,
          logger,
          search = traceSearch,
          solverPool = if (symbolicValues) solverPool else null,
        ) ?: Trace.of(listOf(ExplState.top()), listOf())
      result = SafetyResult.unsafe(trace, proof, statistics)
    } else {
      result = SafetyResult.safe(proof, statistics)
    }
    return result
  }

  /**
   * The initial states as a step from the state where every variable holds the token: init
   * constrains the next-state values, so what it leaves free stays symbolic.
   */
  private fun symbolicInit(
    initExpr: Expr<BoolType>,
    stateSig: hu.bme.mit.delta.java.mdd.MddSignature,
    transSig: hu.bme.mit.delta.java.mdd.MddSignature,
  ): MddHandle {
    val toNext = BasicSubstitution.builder()
    variableOrdering.forEach {
      toNext.put(
        it.getConstDecl(0),
        it.getConstDecl(maxOf(monolithicExpr.transOffsetIndex[it], 1)).ref,
      )
    }
    val initStep =
      transSig.topVariableHandle.checkInNode(
        MddExpressionTemplate.of(
          toNext.build().apply(initExpr),
          { it as Decl<*> },
          solverPool,
          true,
        )
      )
    val levels =
      generateSequence(stateSig.topVariableHandle.variable.orElseThrow()) { it.lower.orElse(null) }
        .toList()
    @Suppress("UNCHECKED_CAST")
    var any: MddNode = (stateSig.topVariableHandle.mddGraph as MddGraph<Any>).getNodeFor(True())
    for (level in levels.reversed()) {
      val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
      when (val type = level.getTraceInfo(Decl::class.java).type) {
        is BoolType -> listOf(0, 1)
        is EnumType -> type.values.map { type.getIntValue(it) }
        else -> listOf(LitExprConverter.token())
      }.forEach { builder.set(it, any) }
      any = level.checkInNode(MddStructuralTemplate.of(builder.buildAndReset()))
    }
    val init =
      RelationalProductProviderImpl(stateSig.variableOrder)
        .compute(any, MddNodeNextStateDescriptor.of(initStep), levels.first())
    return stateSig.topVariableHandle.getHandleFor(init)
  }

  private fun structuralRerun(
    transNodes: List<MddHandle>,
    transSig: hu.bme.mit.delta.java.mdd.MddSignature,
    initNode: MddHandle,
    stateSig: hu.bme.mit.delta.java.mdd.MddSignature,
    ssgTimeMs: Long,
  ) {
    val structDescriptors = mutableListOf<AbstractNextStateDescriptor>()
    val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(transSig.topVariableHandle)
    for (transNode in transNodes) {
      val structTransNode = MddExplicitRepresentationExtractor.transform(transNode, mirrorTop)
      structDescriptors.add(MddNodeNextStateDescriptor.of(structTransNode))
    }
    val structNextStates: AbstractNextStateDescriptor =
      OrNextStateDescriptor.create(structDescriptors)

    val rerunProvider = iterationStrategy.createProvider(stateSig.variableOrder)

    val rerunSolverCountBefore = solverPool.checkCount
    val rerunTime = Stopwatch.createStarted()
    val rerunStateSpace =
      rerunProvider.compute(
        MddNodePostcondition.of(initNode),
        structNextStates,
        stateSig.topVariableHandle,
      )
    rerunTime.stop()
    val rerunSolverCheckCount = solverPool.checkCount - rerunSolverCountBefore
    val rerunStateSpaceSize = MddInterpreter.calculateNonzeroCount(rerunStateSpace)

    val solverTimeMs = ssgTimeMs - rerunTime.elapsedMillis()
    logger.write(Logger.Level.INFO, "Rerun (structural) in: ${rerunTime.elapsedMillis()}\n")
    logger.write(Logger.Level.INFO, "Rerun solver check() calls: $rerunSolverCheckCount\n")
    logger.write(Logger.Level.INFO, "Rerun state space size: $rerunStateSpaceSize\n")
    logger.write(Logger.Level.INFO, "Estimated solver time: ${solverTimeMs}\n")
  }
}
