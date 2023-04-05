package hu.bme.mit.theta.analysis.runtimemonitor

class MonitorCheckpoint internal constructor(private val name: String) {
    private val registeredMonitors : HashSet<Monitor> = HashSet()

    fun registerMonitor(m: Monitor) {
        registeredMonitors.add(m)
    }

    fun runCheckpoint() {
        registeredMonitors.forEach { monitor: Monitor -> monitor.run(name) }
    }
}