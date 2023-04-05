package hu.bme.mit.theta.analysis.runtimemonitor

interface Monitor {
    fun run(checkpointName : String)
}