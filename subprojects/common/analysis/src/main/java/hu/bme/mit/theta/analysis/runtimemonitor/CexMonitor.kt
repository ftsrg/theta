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
package hu.bme.mit.theta.analysis.runtimemonitor

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.runtimemonitor.container.ArgPrecHashStorage
import hu.bme.mit.theta.analysis.runtimemonitor.container.CexHashStorage
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger

class CexMonitor<S : State?, A : Action?, P : Prec?> constructor(
    private val mitigate: Boolean, private val storeArgs : Boolean, private val logger: Logger, private val cegarChecker: CegarChecker<S, A, P>
) : Monitor {
    var lastCex: ArgTrace<S, A>? = null

    private fun disableCoversInTrace() {
        // as we do not know specific counterexamples, disable all cexs - we know none of them are new
        cegarChecker.arg.cexs.forEach { it.nodes().forEach { argNode -> argNode.disableCoveringAbility() } }
    }

    private fun checkIfNewCexFound(): Boolean {
        return if (cegarChecker.arg.getNewCexs(cegarChecker.currentPrec).toList().size > 0) {
            logger.write(Logger.Level.INFO, "\nnew cex found successfully\n")
            true
        } else {
            logger.write(Logger.Level.INFO, "\nNO new cex found, removing covered by edges to infeasible traces\n")
            false
        }
    }

    private fun addNewCounterexample() {
        val newCexs : List<ArgTrace<S,A>> = cegarChecker.arg.getNewCexs(cegarChecker.currentPrec).toList()
        assert(newCexs.size==1, { "Found ${newCexs.size} new cex instead of one" })

        lastCex = newCexs.get(0)
    }

    private fun refinedNewCounterexample() {
        cegarChecker.arg.cexHashStorage.addData(lastCex)
        if(storeArgs) {
            cegarChecker.arg.argPrecHashStorage.addData(Tuple2.of(cegarChecker.arg, cegarChecker.currentPrec))
        }
    }

    private fun throwNotSolvable() {
        throw NotSolvableException()
    }

    override fun execute(checkpointName: String) {
        when (checkpointName) {
            "CegarChecker.unsafeARG" -> if(checkIfNewCexFound()) addNewCounterexample() else throwNotSolvable()
            "StopCriterion.noNewCexFound" -> if(mitigate) { if(!checkIfNewCexFound()) disableCoversInTrace() }
            "SingleExprTraceRefiner.refinedCex" -> refinedNewCounterexample()
            else -> throw RuntimeException("Unknown checkpoint name in CexMonitor execution: $checkpointName")
        }
    }
}

class CexHashStorageObject<S : State, A : Action> {
    val cexHashStorage: CexHashStorage<S, A>? = CexHashStorage<S, A>()
    val argPrecHashStorage: ArgPrecHashStorage<S, A, Prec>? =
        ArgPrecHashStorage<S, A, Prec>() // TODO not the best solution with Prec
}