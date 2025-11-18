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
package hu.bme.mit.theta.analysis.algorithm.mdd

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.*
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.*
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.container.Containers
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool
import java.util.concurrent.*

class MddChecker
@JvmOverloads
constructor(
  private val monolithicExpr: MonolithicExpr,
  private val solverPool: SolverPool,
  private val logger: Logger,
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  private val traceTimeout: Long = 10,
  private val variableOrdering: List<VarDecl<*>> = monolithicExpr.orderVars(),
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  enum class IterationStrategy {
    BFS,
    SAT,
    GSAT,
  }

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())

    val stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph)
    val transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph)

    variableOrdering.forEach {
      Preconditions.checkArgument(
        monolithicExpr.vars.contains(it),
        "Variable ordering contains variable not present in vars List",
      )
    }

    Preconditions.checkArgument(
      variableOrdering.size == Containers.createSet(variableOrdering).size,
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

    val initExpr = PathUtils.unfold(monolithicExpr.initExpr, 0)
    val initNode =
      stateSig.topVariableHandle.checkInNode(
        MddExpressionTemplate.of(initExpr, { it as Decl<*> }, solverPool)
      )

    logger.write(Logger.Level.INFO, "Created initial node\n")

    val transNodes = mutableListOf<MddHandle>()
    val descriptors = mutableListOf<AbstractNextStateDescriptor>()
    for (expr in listOf(monolithicExpr.transExpr)) {
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
    val targetedNextStates = OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode)

    logger.write(Logger.Level.INFO, "Created next-state node, starting fixed point calculation\n")
    val stateSpaceProvider =
      when (iterationStrategy) {
        IterationStrategy.BFS -> {
          BfsProvider(stateSig.variableOrder)
        }
        IterationStrategy.SAT -> {
          SimpleSaturationProvider(stateSig.variableOrder)
        }
        IterationStrategy.GSAT -> {
          GeneralizedSaturationProvider(stateSig.variableOrder)
        }
      }
    val stateSpace =
      stateSpaceProvider.compute(
        MddNodeInitializer.of(initNode),
        targetedNextStates,
        stateSig.topVariableHandle,
      )

    logger.write(Logger.Level.INFO, "Enumerated state-space\n")

    val propViolating = stateSpace.intersection(propNode) as MddHandle

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
      )

    logger.write(Logger.Level.MAINSTEP, "%s\n", statistics)

    // var explTrans = MddExplicitRepresentationExtractor.INSTANCE.transform(transitionNode,
    // transSig.getTopVariableHandle());
    val result: SafetyResult<MddProof, Trace<ExplState, ExprAction>>
    if (violatingSize != 0L) {
      val executor = Executors.newSingleThreadExecutor()
      val future =
        executor.submit<Trace<ExplState, ExprAction>> {
          val reversedDescriptors = mutableListOf<AbstractNextStateDescriptor>()
          for (transNode in transNodes) {
            val explTrans =
              MddExplicitRepresentationExtractor.transform(transNode, transSig.topVariableHandle)
            reversedDescriptors.add(ReverseNextStateDescriptor.of(stateSpace, explTrans))
          }
          val orReversed = OrNextStateDescriptor.create(reversedDescriptors)

          val traceProvider = TraceProvider(stateSig.variableOrder)
          val mddTrace =
            traceProvider.compute(propViolating, orReversed, initNode, stateSig.topVariableHandle)
          val valuations =
            mddTrace
              .map {
                PathUtils.extractValuation(
                  MddValuationCollector.collect(it).stream().findFirst().orElseThrow(),
                  0,
                )
              }
              .toList()
          return@submit Trace.of(
            valuations.stream().map(ExplState::of).toList(),
            monolithicExpr.action(),
          )
        }

      try {
        logger.mainStep("Starting trace generation.\n")
        val trace = future.get(traceTimeout, TimeUnit.SECONDS)
        return SafetyResult.unsafe(trace, MddProof.of(stateSpace), statistics)
      } catch (e: TimeoutException) {
        logger.mainStep("Trace generation timed out, returning empty trace!\n")
        future.cancel(true)
        return SafetyResult.unsafe(
          Trace.of(listOf(ExplState.top()), listOf()),
          MddProof.of(stateSpace),
          statistics,
        )
      } catch (e: InterruptedException) {
        logger.mainStep("Trace generation timed out, returning empty trace!\n")
        future.cancel(true)
        return SafetyResult.unsafe(
          Trace.of(listOf(ExplState.top()), listOf()),
          MddProof.of(stateSpace),
          statistics,
        )
      } catch (e: ExecutionException) {
        throw RuntimeException(e)
      } finally {
        executor.shutdownNow()
      }
    } else {
      result = SafetyResult.safe(MddProof.of(stateSpace), statistics)
    }
    return result
  }
}
