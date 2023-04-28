package hu.bme.mit.theta.analysis.runtimemonitor.container

interface RuntimeDataCollection<T> {
    fun addData(newData: T)
    fun contains(data: T): Boolean?
}
