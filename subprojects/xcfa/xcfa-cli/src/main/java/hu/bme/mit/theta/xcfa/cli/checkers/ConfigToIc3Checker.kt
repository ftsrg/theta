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
import hu.bme.mit.theta.analysis.algorithm.bounded.createMonolithicL2S
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.Ic3Config
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getIc3Checker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

  val ic3Config = config.backendConfig.specConfig as Ic3Config
  val solverFactory: SolverFactory = getSolver(ic3Config.solver, ic3Config.validateSolver)

  val monolithicExpr =
    xcfa
      .toMonolithicExpr(parseContext)
      .let {
        if (config.inputConfig.property == ErrorDetection.TERMINATION)
          it.copy(propExpr = xcfa.initProcedures[0].first.prop).createMonolithicL2S()
        else it
      }
      .let { if (ic3Config.reversed) it.createReversed() else it }

  val baseChecker = { monolithicExpr: MonolithicExpr ->
    Ic3Checker(
      /* monolithicExpr = */ monolithicExpr,
      /* forwardTrace = */ !ic3Config.reversed,
      /* solverFactory = */ solverFactory,
      /* valToState = */ { valuation -> monolithicExpr.valToState.invoke(valuation) },
      /* biValToAction = */ { v1: Valuation, v2: Valuation ->
        monolithicExpr.biValToAction.invoke(v1, v2)
      },
      /* formerFramesOpt = */ true,
      /* unSatOpt = */ true,
      /* notBOpt = */ true,
      /* propagateOpt = */ true,
      /* filterOpt = */ true,
      /* propertyOpt = */ true,
      /* logger = */ logger,
    )
  }

  val checker =
    if (ic3Config.cegar) {
      val cegarChecker =
        MonolithicExprCegarChecker(
          monolithicExpr,
          baseChecker,
          logger,
          getSolver(ic3Config.solver, false),
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
          val result = cegarChecker.check() // states are PredState, actions are XcfaAction
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
          return check(ic3Config.initPrec.predPrec(xcfa))
        }
      }
    } else {
      baseChecker(monolithicExpr)
    }

  return checker
    as SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>
}
