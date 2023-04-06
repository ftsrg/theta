package hu.bme.mit.theta.analysis.runtimemonitor

interface Monitor {
    fun execute(checkpointName : String)
}