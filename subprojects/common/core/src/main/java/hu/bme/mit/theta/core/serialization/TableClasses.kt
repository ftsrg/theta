/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.serialization

import java.util.concurrent.ConcurrentHashMap
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerializationException

/**
 * A class whose objects an [ObjectTable] holds, with the serializer that writes one of them: its
 * generated serializer (or its class's own), never a [ReferenceSerializer]. [instance] is the
 * object of an `object` class, which a format may write as nothing at all.
 */
class TableClass(val cls: Class<*>, serializer: KSerializer<*>, val instance: Any? = null) {
  init {
    require(serializer !is ReferenceSerializer) {
      "${cls.name} is listed with a reference serializer: list its generatedSerializer()"
    }
  }

  @Suppress("UNCHECKED_CAST") val serializer: KSerializer<Any> = serializer as KSerializer<Any>
}

/**
 * The classes an [ObjectTable] can hold, by name (`Class.getName`). Each module lists the ones it
 * declares (core's are [CoreTableClasses]), which spares finding them any reflection. An entry is
 * made when its class is first written or read, so that a run loads only the classes it uses; a
 * test per module checks that the list is complete.
 */
abstract class TableClasses {
  abstract val names: Set<String>

  /** The entry of [name], one of [names]. */
  protected abstract fun entry(name: String): TableClass

  private val made = ConcurrentHashMap<String, TableClass>()

  fun named(name: String): TableClass =
    made.computeIfAbsent(name) {
      if (it !in names) {
        throw SerializationException(
          "$it is not a table class of this build: list it in its module's TableClasses"
        )
      }
      entry(it)
    }

  fun of(cls: Class<*>): TableClass = named(cls.name)

  /** Every entry, which loads every listed class. */
  val all: List<TableClass>
    get() = names.map(::named)

  open operator fun plus(other: TableClasses): TableClasses = Combined(listOf(this, other))

  private class Combined(private val parts: List<TableClasses>) : TableClasses() {
    override val names: Set<String> = parts.flatMapTo(LinkedHashSet()) { it.names }

    init {
      require(names.size == parts.sumOf { it.names.size }) { "A table class is listed twice" }
    }

    override fun entry(name: String): TableClass = parts.first { name in it.names }.named(name)

    override fun plus(other: TableClasses): TableClasses = Combined(parts + other)
  }
}
