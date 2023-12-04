/*
 *  Copyright 2023 Budapest University of Technology and Economics
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