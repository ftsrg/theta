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

import com.google.common.collect.ImmutableSet
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.metadata.EmptyMetaData
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.AnnotateWithWitnessPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.getCMetaData

fun getValidatorChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    return SafetyChecker { _ ->
        // stem check: we can reach a state in the cycle head (TODO Should I also check if cycle head is in recurrent set??)
        val cegarConfig = XcfaConfig<SpecFrontendConfig, CegarConfig>(inputConfig = InputConfig(property = ErrorDetection.CYCLE_HEAD_LOCATION), backendConfig = BackendConfig(backend = Backend.CEGAR, specConfig = CegarConfig()))
        val cegarChecker = getCegarChecker(xcfa, mcm, cegarConfig, logger)
        // val witnessValidationConfig = config.backendConfig.specConfig as WitnessValidationConfig // what to do with this one?

        val stemSafetyResult = cegarChecker.check()

        val monolithicExpr = XcfaMonolithicTransFunc(getCycle(xcfa))
        SafetyResult.unknown()
    }

}

private fun getCycle(xcfa: XCFA): XCFA {
    val builder = XcfaBuilder("cycle")
    val proc = XcfaProcedureBuilder("cycle", ProcedurePassManager())
    builder.addEntryPoint(proc, listOf())

    val hondaLineStart = AnnotateWithWitnessPass.witness.getHonda()!!.location.line
    val hondaColumnStart = AnnotateWithWitnessPass.witness.getHonda()!!.location.column

    proc.createInitLoc(EmptyMetaData)
    val honda: XcfaLocation? = xcfa.initProcedures.first().first.locs.find {
        val outEdgeMetadata = it.outgoingEdges.firstOrNull()?.getCMetaData()
        (outEdgeMetadata != null
                && outEdgeMetadata.lineNumberStart == hondaLineStart
                && outEdgeMetadata.colNumberStart == hondaColumnStart)
    }
    if(honda == null) error("Honda does not exist at $hondaLineStart:${hondaColumnStart?.plus(1)}")
    proc.addLoc(honda)
    proc.addEdge(XcfaEdge(proc.initLoc, honda, EmptyMetaData))
    for (outgoingEdge in honda.outgoingEdges) {
        buildCycleXcfa(honda, proc, outgoingEdge.target, setOf(honda, outgoingEdge.target), setOf(outgoingEdge))
    }
    return builder.build()
}

private fun buildCycleXcfa(honda: XcfaLocation, proc: XcfaProcedureBuilder, loc: XcfaLocation, reachedSet: Set<XcfaLocation>, edges: Set<XcfaEdge>) {
    for (outgoingEdge in loc.outgoingEdges) {
        val outLoc = outgoingEdge.target
        if(outLoc == honda) {
            reachedSet.forEach(proc::addLoc)
            edges.forEach(proc::addEdge)
        } else if (!reachedSet.contains(outLoc)) {
            buildCycleXcfa(
                honda,
                proc,
                outLoc,
                ImmutableSet.builder<XcfaLocation>().addAll(reachedSet).add(outLoc).build(),
                ImmutableSet.builder<XcfaEdge>().addAll(edges).add(outgoingEdge).build()
            )
        }
    }
}