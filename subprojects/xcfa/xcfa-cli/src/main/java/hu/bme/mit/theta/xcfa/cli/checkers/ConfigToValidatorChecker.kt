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
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.AnnotateWithWitnessPass

fun getValidatorChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    val cegarConfig = XcfaConfig<SpecFrontendConfig, CegarConfig>(inputConfig = InputConfig(property = ErrorDetection.CYCLE_HEAD_LOCATION), backendConfig = BackendConfig(backend = Backend.CEGAR, specConfig = CegarConfig()))
    val cegarChecker = getCegarChecker(xcfa, mcm, cegarConfig, logger)
    val witnessValidationConfig = config.backendConfig.specConfig as WitnessValidationConfig
    return SafetyChecker { _ ->

        // stem check: we can reach a state in the cycle head which is in the recurrent set

        SafetyResult.unknown()
    }

}