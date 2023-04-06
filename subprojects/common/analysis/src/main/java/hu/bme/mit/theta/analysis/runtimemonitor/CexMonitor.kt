package hu.bme.mit.theta.analysis.runtimemonitor

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.ArgTrace
import hu.bme.mit.theta.analysis.runtimemonitor.container.CexHashStorage
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import java.lang.RuntimeException


// TODO implement mitigation
class CexMonitor<S : State?, A : Action?> constructor(
    private val mitigate: Boolean, private val logger: Logger, private val arg: ARG<S, A>
) : Monitor {
    private val cexHashStorage = CexHashStorage<S, A>()
    var lastCex: ArgTrace<S, A>? = null

    fun checkIfNewCexFound(): Boolean {
        return if (arg.cexs.anyMatch { cex -> !cexHashStorage.contains(cex) }) {
            logger.write(Logger.Level.VERBOSE, "Counterexample hash check: new cex found successfully")
            true
        } else {
            logger.write(Logger.Level.INFO, "Counterexample hash check: NO new cex found")
            false
        }
    }

    fun addNewCounterexample() {
        val newCexs : List<ArgTrace<S,A>> = arg.cexs.filter { !cexHashStorage.contains(it) }.toList()
        assert(newCexs.size==1, { "Found ${newCexs.size} new cex instead of one" })

        lastCex = newCexs.get(0)
        cexHashStorage.addData(lastCex)
    }

    private fun throwNotSolvable() {
        throw NotSolvableException()
    }

    override fun execute(checkpointName: String) {
        when (checkpointName) {
            "CegarChecker.unsafeARG" -> if(checkIfNewCexFound()) addNewCounterexample() else throwNotSolvable()
            else -> throw RuntimeException("Unknown checkpoint name in CexMonitor execution: $checkpointName")
        }
    }
}
