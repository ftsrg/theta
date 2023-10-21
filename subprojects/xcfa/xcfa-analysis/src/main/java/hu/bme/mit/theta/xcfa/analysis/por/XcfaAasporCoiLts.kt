package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.coi.transFuncVersion
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

class XcfaAasporCoiLts(
    xcfa: XCFA,
    ignoredVarRegistry: MutableMap<Decl<out Type>, MutableSet<ExprState>>,
    coiLTS: LTS<XcfaState<*>, XcfaAction>
) : XcfaAasporLts(xcfa, ignoredVarRegistry) {

    init {
        simpleXcfaLts = coiLTS
    }

    override fun getEdgeOf(action: XcfaAction): XcfaEdge =
        super.getEdgeOf(action.transFuncVersion ?: action)

    override fun isBackwardAction(action: XcfaAction): Boolean =
        backwardTransitions.any { it.source == action.edge.source && it.target == action.edge.target }
}