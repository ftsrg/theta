package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.transFuncVersion
import hu.bme.mit.theta.xcfa.model.XCFA

class XcfaAasporCoiLts(
    xcfa: XCFA,
    ignoredVarRegistry: MutableMap<Decl<out Type>, MutableSet<ExprState>>,
    coiLTS: LTS<XcfaState<*>, XcfaAction>
) : XcfaAasporLts(xcfa, ignoredVarRegistry) {

    init {
        simpleXcfaLts = coiLTS
    }

    override fun getPersistentSetFirstActions(allEnabledActions: Collection<XcfaAction>): List<List<XcfaAction>> {
        val actions = super.getPersistentSetFirstActions(allEnabledActions)
        return actions.map { a -> a.map { it.transFuncVersion ?: it } }
    }
}