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
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getBoundedChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    val boundedConfig = config.backendConfig.specConfig as BoundedConfig

    return BoundedChecker(
        monolithicExpr = xcfa.toMonolithicExpr(),
        bmcSolver = tryGetSolver(boundedConfig.bmcConfig.bmcSolver,
            boundedConfig.bmcConfig.validateBMCSolver)?.createSolver(),
        bmcEnabled = { !boundedConfig.bmcConfig.disable },
        lfPathOnly = { !boundedConfig.bmcConfig.nonLfPath },
        itpSolver = tryGetSolver(boundedConfig.itpConfig.itpSolver,
            boundedConfig.itpConfig.validateItpSolver)?.createItpSolver(),
        imcEnabled = { !boundedConfig.itpConfig.disable },
        indSolver = tryGetSolver(boundedConfig.indConfig.indSolver,
            boundedConfig.indConfig.validateIndSolver)?.createSolver(),
        kindEnabled = { !boundedConfig.indConfig.disable },
        valToState = { xcfa.valToState(it) },
        biValToAction = { val1, val2 -> xcfa.valToAction(val1, val2) },
        logger = logger
    ) as SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>

}

private fun tryGetSolver(name: String, validate: Boolean): SolverFactory? {
    try {
        return getSolver(name, validate)
    } catch (e: Throwable) {
        return null
    }
}