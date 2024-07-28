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
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.metadata.EmptyMetaData
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.valToAction
import hu.bme.mit.theta.xcfa.cli.utils.valToState
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.AnnotateWithWitnessPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.getCMetaData

fun getValidatorChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    fun getHonda(): XcfaLocation {
        val hondaLineStart = AnnotateWithWitnessPass.witness.getHonda()!!.location.line
        val hondaColumnStart = AnnotateWithWitnessPass.witness.getHonda()!!.location.column

        val honda: XcfaLocation? = xcfa.initProcedures.first().first.locs.find {
            val outEdgeMetadata = it.outgoingEdges.firstOrNull()?.getCMetaData()
            (outEdgeMetadata != null
                && outEdgeMetadata.lineNumberStart == hondaLineStart
                && outEdgeMetadata.colNumberStart == hondaColumnStart)
        }
        return honda ?: error("Honda does not exist at $hondaLineStart:${hondaColumnStart?.plus(1)}")
    }

    return SafetyChecker { _ ->
        // stem check: we can reach a state in the cycle head (TODO Should I also check if cycle head is in recurrent set??)
        val cegarConfig = XcfaConfig<SpecFrontendConfig, CegarConfig>(inputConfig = InputConfig(property = ErrorDetection.CYCLE_HEAD_LOCATION), backendConfig = BackendConfig(backend = Backend.CEGAR, specConfig = CegarConfig()))
        val cegarChecker = getCegarChecker(xcfa, mcm, cegarConfig, logger)
        // val witnessValidationConfig = config.backendConfig.specConfig as WitnessValidationConfig // what to do with this one?

        val stemSafetyResult = cegarChecker.check()

        val recurrentSetExpr = True() // TODO: get this from the witness
        val hondaLoc = getHonda()
        val varsMatch = And(xcfa.collectVars().map { Eq(it.ref, Var("__THETA_saved_" + it.name, it.type).ref) })
        val monolithicExpr = XcfaMonolithicTransFunc(
            xcfa,
            hondaLoc,
            setOf(hondaLoc),
            And(varsMatch, recurrentSetExpr),
            And(varsMatch, recurrentSetExpr)
        )
        val boundedChecker = BoundedChecker(
            monolithicExpr.toMonolithicExpr(),
            bmcSolver = Z3SolverFactory.getInstance().createSolver(),
            indSolver = Z3SolverFactory.getInstance().createSolver(),
            lfPathOnly = { true },
            kindEnabled = { true },
            imcEnabled = { false },
            valToState = { valToState(xcfa, monolithicExpr.locMap, it) as XcfaState<PtrState<*>> },
            biValToAction = { val1, val2 ->
                valToAction(
                    xcfa, val1, val2, monolithicExpr.locMap, monolithicExpr.callsiteMap
                )
            },
            logger = logger
        )

        val cycleSafetyResult = boundedChecker.check() // if safe, there is a no loop

        if (cycleSafetyResult.isUnsafe && stemSafetyResult.isUnsafe) {
            cycleSafetyResult
        } else if (cycleSafetyResult.isSafe) {
            cycleSafetyResult
        } else {
            SafetyResult.safe(EmptyWitness.getInstance())
        }
    }

}

private fun getCycle(xcfa: XCFA): XCFA {
    val proc = XcfaProcedureBuilder("cycle", ProcedurePassManager())

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
    return xcfa.substituteInitProc(proc.build(xcfa), listOf())
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