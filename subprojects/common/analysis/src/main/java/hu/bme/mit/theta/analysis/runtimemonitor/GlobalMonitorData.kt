package hu.bme.mit.theta.analysis.runtimemonitor

object GlobalMonitorData {
    private var newCexInArg : Boolean = true // default value is true and it is only actually updated if mitigation is on

    fun updateNewCexInArg(newCexInArg : Boolean) {
        this.newCexInArg = newCexInArg
    }

    fun isNewCexInArg(): Boolean {
        return newCexInArg
    }
}
