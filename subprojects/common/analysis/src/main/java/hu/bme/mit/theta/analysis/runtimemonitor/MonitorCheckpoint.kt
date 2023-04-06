package hu.bme.mit.theta.analysis.runtimemonitor

/**
 * This class handles the creation, registering and execution of monitor checkpoints.
 * If you would like to add a new checkpoint do the following:
 * 1, Add its name below to checkpointNames in the companion object
 *      (from then on it will be automatically created)
 * 2, Wherever you would like to execute it, add a MonitorCheckpoint.execute(<name>) call
 * 3, Register your monitors to it so they are executed when the checkpoint is executed: (MonitorCheckpoint.register)
 */
class MonitorCheckpoint internal constructor(private val name: String) {
    private val registeredMonitors : HashSet<Monitor> = HashSet()

    fun registerMonitor(m: Monitor) {
        registeredMonitors.add(m)
    }

    fun executeCheckpoint() {
        registeredMonitors.forEach { monitor: Monitor -> monitor.execute(name) }
    }

    companion object Checkpoints {
        // Add any new checkpoints here
        private val checkpointNames = setOf(
            "CegarChecker.unsafeARG",
        )

        private val registeredCheckpoints : HashMap<String, MonitorCheckpoint> = HashMap()

        init {
            checkpointNames.forEach { registeredCheckpoints.put(it, MonitorCheckpoint(it)) }
        }

        fun register(m: Monitor, checkpointName: String) {
            assert(registeredCheckpoints.contains(checkpointName))
            { "Checkpoint name $checkpointName was not registered (add it in MonitorCheckpoint.kt)" } // see checkpointNames above
            registeredCheckpoints.get(checkpointName)!!.registerMonitor(m)
        }

        fun execute(name: String) {
            assert(registeredCheckpoints.contains(name))
                { "Checkpoint name $name was not registered (add it in MonitorCheckpoint.kt)" } // see checkpointNames above
            registeredCheckpoints[name]!!.executeCheckpoint()
        }
    }
}