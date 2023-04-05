package hu.bme.mit.theta.analysis.runtimemonitor

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.ArgTrace
import hu.bme.mit.theta.analysis.runtimemonitor.container.CexHashStorage
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import java.lang.RuntimeException

class CexMonitor<S : State?, A : Action?> internal constructor(
    private val mitigate: Boolean, private val logger: Logger, private val arg: ARG<S, A> // TODO register checkpoints
) : Monitor {
    private val cexHashStorage = CexHashStorage<S, A>()
    var lastCex: ArgTrace<S, A>? = null
        private set

    fun checkIfCounterexampleNew(cex: ArgTrace<S, A>?): Boolean {
        return if (cexHashStorage.contains(cex)) {
            logger.write(Logger.Level.INFO, "Counterexample hash check: cex NOT new")
            false
        } else {
            logger.write(Logger.Level.VERBOSE, "Counterexample hash check: cex is new")
            true
        }
    }

    fun addCounterexample(cex: ArgTrace<S, A>?) {
        lastCex = cex
        cexHashStorage.addData(cex)
    }

    private fun throwNotSolvable() {
        throw NotSolvableException()
    }

    override fun run(checkpointName: String) {
        when (checkpointName) {
            "CegarChecker.unsafeARG" -> if(checkIfCounterexampleNew(TODO())) throwNotSolvable()
            else -> throw RuntimeException("Unknown checkpoint name in CexMonitor execution: $checkpointName")
        }
    }
}
