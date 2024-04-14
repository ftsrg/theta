package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.XCFA

internal class XcfaOcCorrectnessValidator(
    decisionProcedure: OcDecisionProcedureType,
    private val xcfa: XCFA,
    private val ocChecker: OcChecker<E>,
    private val threads: Set<Thread>,
    private val events: Map<VarDecl<*>, Map<Int, List<E>>>,
    private val violations: List<Violation>,
    private val pos: List<R>,
    private val rfs: Map<VarDecl<*>, List<R>>
) {

    internal val ocCorrectnessValidator: OcChecker<E> = decisionProcedure.checker()

    fun validate(): Boolean {
        check(ocChecker.solver.status.isUnsat)

        val propagated = ocChecker.getPropagatedClauses()
        val reasons = ocChecker.getRelations()
        propagated.filter { clause ->

            TODO()
        }
        TODO()
    }
}