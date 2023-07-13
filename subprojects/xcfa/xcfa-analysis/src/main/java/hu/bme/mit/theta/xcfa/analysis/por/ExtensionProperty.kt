package hu.bme.mit.theta.xcfa.analysis.por

import java.util.*
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty

fun <R, T> extension() = ExtensionProperty<R, T>()
fun <R, T> nullableExtension() = NullableExtensionProperty<R, T?>()

class ExtensionProperty<R, T> : ReadWriteProperty<R, T> {

    private val map = IdentityHashMap<R, T>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]!!
    override fun setValue(thisRef: R, property: KProperty<*>, value: T) {
        map[thisRef] = value
    }
}

open class NullableExtensionProperty<R, T> : ReadWriteProperty<R, T?> {

    protected val map = IdentityHashMap<R, T?>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]
    override fun setValue(thisRef: R, property: KProperty<*>, value: T?) {
        map[thisRef] = value
    }

    fun clear() = map.clear()
}
