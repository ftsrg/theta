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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.*
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.*

fun getBoundedChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

  val boundedConfig = config.backendConfig.specConfig as BoundedConfig

  val monolithicExpr =
    xcfa.toMonolithicExpr(parseContext).let {
      if (boundedConfig.reversed) it.createReversed() else it
    }

  val baseChecker = { monolithicExpr: MonolithicExpr ->
    BoundedChecker(
      monolithicExpr = monolithicExpr,
      bmcSolver =
        tryGetSolver(boundedConfig.bmcConfig.bmcSolver, boundedConfig.bmcConfig.validateBMCSolver)
          ?.createSolver(),
      bmcEnabled = { !boundedConfig.bmcConfig.disable },
      lfPathOnly = { !boundedConfig.bmcConfig.nonLfPath },
      itpSolver =
        tryGetSolver(boundedConfig.itpConfig.itpSolver, boundedConfig.itpConfig.validateItpSolver)
          ?.createItpSolver(),
      imcEnabled = { !boundedConfig.itpConfig.disable },
      indSolver =
        tryGetSolver(boundedConfig.indConfig.indSolver, boundedConfig.indConfig.validateIndSolver)
          ?.createSolver(),
      kindEnabled = { !boundedConfig.indConfig.disable },
      valToState = monolithicExpr.valToState,
      biValToAction = monolithicExpr.biValToAction,
      logger = logger,
    )
  }

  val checker =
    if (boundedConfig.cegar) {
      val cegarChecker =
        MonolithicExprCegarChecker(
          monolithicExpr,
          baseChecker,
          logger,
          getSolver(boundedConfig.bmcConfig.bmcSolver, false),
        )
      object :
        SafetyChecker<
          EmptyProof,
          Trace<XcfaState<PtrState<PredState>>, XcfaAction>,
          XcfaPrec<PtrPrec<PredPrec>>,
        > {
        override fun check(
          initPrec: XcfaPrec<PtrPrec<PredPrec>>
        ): SafetyResult<EmptyProof, Trace<XcfaState<PtrState<PredState>>, XcfaAction>> {
          val result =
            cegarChecker.check(initPrec.p.innerPrec) // states are PredState, actions are XcfaAction
          if (result.isUnsafe) {
            val cex = result.asUnsafe().cex as Trace<PredState, XcfaAction>
            val locs =
              (0 until cex.length()).map { i -> cex.actions[i].source } +
                cex.actions[cex.length() - 1].target
            val states = locs.mapIndexed { i, it -> XcfaState(xcfa, it, PtrState(cex.states[i])) }
            return SafetyResult.unsafe(Trace.of(states, cex.actions), result.proof)
          } else
            return result
              as SafetyResult<EmptyProof, Trace<XcfaState<PtrState<PredState>>, XcfaAction>>
        }

        override fun check():
          SafetyResult<EmptyProof, Trace<XcfaState<PtrState<PredState>>, XcfaAction>> {
          return check(boundedConfig.initPrec.predPrec(xcfa))
        }
      }
    } else {
      baseChecker(monolithicExpr)
    }

  return checker
    as SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>
}

private fun tryGetSolver(name: String, validate: Boolean): SolverFactory? {
  try {
    return getSolver(name, validate)
  } catch (e: Throwable) {
    return null
  }
}
