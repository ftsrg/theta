package hu.bme.mit.theta.xcfa.analysis.coi

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation

class XcfaCoiSingleThread(xcfa: XCFA) : XcfaCoi(xcfa) {

    private var observed: Set<Pair<XcfaLocation, XcfaLocation>> = setOf()

    override val lts = object : LTS<S, A> {
        override fun getEnabledActionsFor(state: S): Collection<A> {
            val enabled = coreLts.getEnabledActionsFor(state)
            return lastPrec?.let { replaceIrrelevantActions(enabled, it) } ?: enabled
        }

        override fun <P : Prec> getEnabledActionsFor(state: S, explored: Collection<A>, prec: P): Collection<A> {
            if (lastPrec != prec) reinitialize(prec)
            val enabled = coreLts.getEnabledActionsFor(state, explored, prec)
            return replaceIrrelevantActions(enabled, prec)
        }

        private fun replaceIrrelevantActions(enabled: Collection<A>, prec: Prec): Collection<A> =
            enabled.map { action ->
                if (Pair(action.source, action.target) !in observed) {
                    replace(action, prec)
                } else {
                    action.transFuncVersion = null
                    action
                }
            }
    }

    fun reinitialize(prec: Prec) {
        lastPrec = prec
        directObservation.clear()
        val realObservers = mutableSetOf<XcfaEdgeWrapper>()
        xcfa.procedures.forEach { procedure ->
            procedure.edges.forEach { edge ->
                findDirectObservers(edge, prec)
                if (isRealObserver(edge)) {
                    realObservers.add(edge.wrapper)
                }
            }
        }
        collectedObservedEdges(realObservers)
    }

    override fun addToRelation(source: XcfaEdge, target: XcfaEdge,
        relation: MutableMap<XcfaEdgeWrapper, MutableSet<XcfaEdgeWrapper>>) {
        val sourceW = source.wrapper
        val targetW = target.wrapper
        relation[targetW] = relation[targetW] ?: mutableSetOf()
        relation[targetW]!!.add(sourceW)
    }

    private fun collectedObservedEdges(realObservers: Set<XcfaEdgeWrapper>) {
        val toVisit = realObservers.toMutableList()
        val visited = mutableSetOf<XcfaEdgeWrapper>()
        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.removeFirst()
            visited.add(visiting)
            val toAdd = directObservation[visiting] ?: emptySet()
            toVisit.addAll(toAdd.filter { it !in visited })
        }
        observed = visited.map { it.source to it.target }.toSet()
    }
}