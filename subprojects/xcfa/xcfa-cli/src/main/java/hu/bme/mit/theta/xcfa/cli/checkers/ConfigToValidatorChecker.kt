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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.valToAction
import hu.bme.mit.theta.xcfa.cli.utils.valToState
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.AnnotateWithWitnessPass
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

        val boundedChecker =
            tryGetSimpleChecker(xcfa, hondaLoc, recurrentSetExpr, logger) ?: getProperBoundedChecker(
                xcfa, hondaLoc, recurrentSetExpr, logger
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

private fun getProperBoundedChecker(
    xcfa: XCFA, hondaLoc: XcfaLocation, recurrentSetExpr: Expr<BoolType>, logger: Logger
): BoundedChecker<XcfaState<PtrState<*>>, XcfaAction> {
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
        imcEnabled = { false },
        kindEnabled = { false },
        valToState = { valToState(xcfa, monolithicExpr.locMap, it) as XcfaState<PtrState<*>> },
        biValToAction = { val1, val2 ->
            valToAction(
                xcfa, val1, val2, monolithicExpr.locMap, monolithicExpr.callsiteMap
            )
        },
        logger = logger
    )
    return boundedChecker
}

private fun tryGetSimpleChecker(
    xcfa: XCFA, honda: XcfaLocation, recurrentSetExpr: Expr<BoolType>, logger: Logger
): SafetyChecker<EmptyWitness, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>? {
    val defaultIndex = VarIndexingFactory.indexing(0)
    val stmt = buildCycleStmt(honda, honda, setOf(honda), setOf()) ?: return null
    val vars = StmtUtils.getVars(stmt)
    val varsMatch = And(
        vars.map { Eq(it.ref, Var("__THETA_saved_" + it.name, it.type).ref) } +
            recurrentSetExpr
    )

    val beginning = PathUtils.unfold(varsMatch, defaultIndex)

    val solver = Z3SolverFactory.getInstance().createSolver()
    var index = defaultIndex
    solver.add(PathUtils.unfold(beginning, index))
    var i = 0;
    while (true) {
        val unfoldResult = StmtUtils.toExpr(stmt, index)
        val afterIndex = unfoldResult.indexing
        val expr = And(unfoldResult.exprs)
        val end = PathUtils.unfold(varsMatch, afterIndex)

        solver.add(PathUtils.unfold(expr, index))
        index = afterIndex
        WithPushPop(solver).use {
            solver.add(PathUtils.unfold(end, index))
            logger.write(Logger.Level.SUBSTEP, "BMC iteration #${i++}\n")
            if (solver.check().isSat) {
                return SafetyChecker { _ ->
                    SafetyResult.unsafe(
                        Trace.of(listOf(XcfaState(null, emptyMap(), PtrState(ExplState.top()))), listOf()),
                        EmptyWitness.getInstance()
                    )
                }
            }
        }
    }
}

private fun buildCycleStmt(
    honda: XcfaLocation, loc: XcfaLocation, reachedSet: Set<XcfaLocation>, edges: Set<XcfaEdge>
): NonDetStmt? {
    val stmts = ArrayList<Stmt>()
    for (outgoingEdge in loc.outgoingEdges) {
        val outLoc = outgoingEdge.target
        if(outLoc == honda) {
            val labels = edges.flatMap { it.getFlatLabels() }
            if (labels.any { it !is StmtLabel && it !is NopLabel }) {
                return null
            }
            return NonDetStmt.of(listOf(SequenceStmt.of(labels.map { it.toStmt() })))
        } else if (!reachedSet.contains(outLoc)) {
            buildCycleStmt(
                honda,
                outLoc,
                ImmutableSet.builder<XcfaLocation>().addAll(reachedSet).add(outLoc).build(),
                ImmutableSet.builder<XcfaEdge>().addAll(edges).add(outgoingEdge).build()
            )?.also { stmts.addAll(it.stmts) }
        }
    }
    return if (stmts.isNotEmpty()) NonDetStmt.of(stmts) else null
}