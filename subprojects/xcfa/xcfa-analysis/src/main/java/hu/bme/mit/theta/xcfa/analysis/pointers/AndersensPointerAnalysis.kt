package hu.bme.mit.theta.xcfa.analysis.pointers

import hu.bme.mit.theta.core.utils.PointerStore
import hu.bme.mit.theta.xcfa.model.XCFA

class AndersensPointerAnalysis : PointerAnalysis() {
    override fun run(xcfa: XCFA): PointerStore {
        val actions = getPointerActions(xcfa)
        return runOnActions(actions)
    }

    override fun runOnActions(actions: List<PointerAction>): PointerStore {
        val pointerStore = PointerStore()

        while (true) {
            val edgeCount = pointerStore.edgeCount()
            actions.forEach { action ->
                val pVarDecl = action.p
                val qVarDecl = action.q
                when (action) {
                    is ReferencingPointerAction -> {
                        // p = &q
                        pointerStore.addPointsTo(pVarDecl, qVarDecl)
                    }
                    is DereferencingWritePointerAction -> {
                        // *p = q
                        val xs = pointerStore.pointsTo(pVarDecl)
                        xs.forEach { x ->
                            pointerStore.pointsTo(qVarDecl).forEach { y ->
                                if (x != y) pointerStore.addPointsTo(x, y)
                            }
                        }
                    }
                    is DereferencingReadPointerAction -> {
                        // p = *q
                        val xs = pointerStore.pointsTo(qVarDecl)
                        xs.forEach { x ->
                           pointerStore.pointsTo(x).forEach { y ->
                               if (pVarDecl != y) pointerStore.addPointsTo(pVarDecl, y)
                            }
                        }
                    }
                    is AliasingPointerAction -> {
                        // p = q
                        pointerStore.pointsTo(qVarDecl).forEach { y ->
                            if (pVarDecl != y) pointerStore.addPointsTo(pVarDecl, y)
                        }
                    }
                }
            }
            if (pointerStore.edgeCount() == edgeCount) {
                break
            }
        }
        return pointerStore
    }
}