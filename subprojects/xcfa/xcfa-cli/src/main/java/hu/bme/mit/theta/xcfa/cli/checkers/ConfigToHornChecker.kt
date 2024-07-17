/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.HornConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa2chc.toCHC
import org.abego.treelayout.internal.util.Contract.checkState

fun getHornChecker(xcfa: XCFA, mcm: MCM, config: XcfaConfig<*, *>, logger: Logger):
    SafetyChecker<EmptyWitness, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    checkState(xcfa.isInlined, "Only inlined XCFAs work right now")
    checkState(xcfa.initProcedures.size == 1, "Only one-procedure XCFAs work right now")

    val hornConfig = config.backendConfig.specConfig as HornConfig

    val checker = HornChecker(
        relations = xcfa.initProcedures[0].first.toCHC(),
        hornSolverFactory = getSolver(hornConfig.solver, hornConfig.validateSolver),
        logger = logger,
    )

    return SafetyChecker<EmptyWitness, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
        val result = checker.check(null)

        if (result.isSafe) {
            SafetyResult.safe(EmptyWitness.getInstance())
        } else if (result.isUnsafe) {
            val proof = result.asUnsafe().cex
            val state = XcfaState<PtrState<PredState>>(xcfa, mapOf(), PtrState(PredState.of(proof.proofNode.expr)))
            SafetyResult.unsafe(Trace.of(listOf(state), listOf()), EmptyWitness.getInstance())
        } else {
            SafetyResult.unknown()
        }
    }

}