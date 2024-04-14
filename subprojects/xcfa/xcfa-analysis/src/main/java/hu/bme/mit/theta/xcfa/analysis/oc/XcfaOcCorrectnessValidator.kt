package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation

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

        val validConflicts = ocChecker.getPropagatedClauses().filter { checkCycle(it) }
        ocCorrectnessValidator.solver.add(validConflicts.map { Not(it.expr) })
        return ocCorrectnessValidator.check(events, pos, rfs)?.isUnsat == true
    }

    private fun checkCycle(combinedReason: Reason): Boolean {
        if (combinedReason.reasons.isEmpty()) return false
        var firstEdge: XcfaEdge? = null
        var previousEdge: XcfaEdge? = null
        combinedReason.reasons.forEach { r ->
            when (r) {
                is PoReason -> {}
                is RelationReason<*> -> {
                    r as RelationReason<E>
                    val from = r.relation.from.edge
                    val to = r.relation.to.edge

                    if(!isPo(previousEdge, from)) return false

                    if (firstEdge == null) firstEdge = from
                    previousEdge = to
                }

                is FromReadReason<*> -> TODO()
                is WriteSerializationReason<*> -> TODO()
                else -> error("Nested combined reasons or other reasons not supported.")
            }
        }
        return true
    }

    private fun isPo(from: XcfaEdge?, to: XcfaEdge): Boolean {
        from ?: return true

    }

    private object ReachableEdges {
        private typealias Edge = Pair<XcfaLocation, XcfaLocation>
        private val map: MutableMap<Edge, List<Edge>> = mutableMapOf()

        operator fun get(edge: XcfaEdge): List<Edge> = map.getOrPut(edge.source to edge.target) {

        }
    }
}