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

import hu.bme.mit.theta.core.type.Type
import java.util.IdentityHashMap
import kotlinx.serialization.ContextualSerializer
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerializationException
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.AbstractEncoder
import kotlinx.serialization.encoding.CompositeDecoder
import kotlinx.serialization.encoding.CompositeEncoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.decodeStructure
import kotlinx.serialization.encoding.encodeStructure
import kotlinx.serialization.modules.SerializersModule

/**
 * The identity table of one encode or decode. Types, declarations, expressions and statements (and
 * whatever else a client refers to by reference, e.g. C types) are written once, each with the
 * serializer its class is listed with in [tableClasses], and referred to by index everywhere else:
 * shared subexpressions stay shared and a declaration stays one object.
 *
 * Encoding runs twice over the same object. The first pass ([collect]) interns every reachable
 * object, children before parents; the second writes the table before anything that refers to it.
 * Decoding therefore resolves every reference on the spot.
 */
class ObjectTable
private constructor(
  val module: SerializersModule,
  private val tableClasses: TableClasses,
  private val internKey: (Any) -> Any?,
  ambient: List<Any>,
  private var collecting: Boolean,
) {

  private val ambient = ambient.toMutableList()
  private val ids = IdentityHashMap<Any, Int>()
  private val equalIds = HashMap<Any, Int>()
  private val classIds = HashMap<Class<*>, Int>()

  /** The objects in table order: every object comes after the ones it refers to. */
  val values = ArrayList<Any>()

  private val classes = ArrayList<TableClass>()
  private val entryClasses = ArrayList<Int>()

  fun idOf(value: Any): Int {
    ids[value]?.let {
      return it
    }
    val key = internKey(value)
    if (key != null) {
      equalIds[key]?.let {
        ids[value] = it
        return it
      }
    }
    check(collecting) { "Not collected in the first pass: ${value.javaClass.name} $value" }
    CollectingEncoder(module).encodeSerializableValue(definition(value.javaClass), value)
    // The definition may have interned the children first, so the id is assigned only now.
    val id = values.size
    values.add(value)
    entryClasses.add(classId(value.javaClass))
    ids[value] = id
    if (key != null) equalIds[key] = id
    return id
  }

  fun valueAt(id: Int): Any = values[id]

  /**
   * The object of [cls] that everything in this table shares without serializing it (e.g. the parse
   * context of the C types), see [AmbientSerializer].
   */
  fun <T : Any> ambient(cls: Class<T>): T =
    cls.cast(ambient.firstOrNull { cls.isInstance(it) } ?: error("No ambient ${cls.simpleName}"))

  /** Makes [value] ambient, e.g. once decoding has read it. */
  fun addAmbient(value: Any) {
    ambient.add(value)
  }

  /**
   * [value]'s serialized state with its references as indices: equal keys mean interchangeable
   * objects. Interns what [value] refers to.
   */
  fun definitionKey(value: Any): Any =
    KeyEncoder(module).also { it.encodeSerializableValue(definition(value.javaClass), value) }.key

  /** Runs [serializer] over [value] without output, interning everything it refers to. */
  fun <T> collect(serializer: KSerializer<T>, value: T) {
    check(collecting) { "The table is already complete" }
    CollectingEncoder(module).encodeSerializableValue(serializer, value)
  }

  /**
   * Ends the first pass: from now on, referring to an object that was not collected is an error.
   */
  fun complete() {
    collecting = false
  }

  private fun classId(cls: Class<*>): Int =
    classIds.getOrPut(cls) {
      classes.add(tableClasses.of(cls))
      classes.size - 1
    }

  /** The serializer that writes an object of [cls] itself, its references kept as references. */
  private fun definition(cls: Class<*>): KSerializer<Any> = tableClasses.of(cls).serializer

  private object EntrySerializer : KSerializer<Any> {
    @OptIn(ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("theta.ObjectTable.Entry") {
        element("class", Int.serializer().descriptor)
        element("value", ContextualSerializer(Any::class).descriptor)
      }

    override fun serialize(encoder: Encoder, value: Any) {
      val table = current()
      val id = table.ids.getValue(value)
      encoder.encodeStructure(descriptor) {
        encodeIntElement(descriptor, 0, table.entryClasses[id])
        encodeSerializableElement(descriptor, 1, table.definition(value.javaClass), value)
      }
    }

    override fun deserialize(decoder: Decoder): Any {
      val table = current()
      var cls: TableClass? = null
      var value: Any? = null
      decoder.decodeStructure(descriptor) {
        while (true) {
          when (val index = decodeElementIndex(descriptor)) {
            0 -> cls = table.classes[decodeIntElement(descriptor, 0)]
            1 -> {
              val c = checkNotNull(cls) { "An object table entry must name its class first" }
              value = decodeSerializableElement(descriptor, 1, c.serializer)
            }
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unexpected object table entry element $index")
          }
        }
      }
      // A format may leave out an empty value, i.e. the one of an object.
      val c = checkNotNull(cls) { "An object table entry must name its class" }
      return value ?: c.instance ?: error("Entry of ${c.cls.name} has no value")
    }
  }

  /** Writes the class names and the entries; decoding appends each entry as soon as it is read. */
  object Serializer : KSerializer<ObjectTable> {
    private val classNames = ListSerializer(String.serializer())
    private val entries = ListSerializer(EntrySerializer)

    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("theta.ObjectTable") {
        element("classes", classNames.descriptor)
        element("entries", entries.descriptor)
      }

    override fun serialize(encoder: Encoder, value: ObjectTable) {
      check(!value.collecting) { "The object table must be completed before it is written" }
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, classNames, value.classes.map { it.cls.name })
        encodeSerializableElement(descriptor, 1, entries, value.values)
      }
    }

    override fun deserialize(decoder: Decoder): ObjectTable {
      val table = current()
      decoder.decodeStructure(descriptor) {
        while (true) {
          when (val index = decodeElementIndex(descriptor)) {
            0 ->
              decodeSerializableElement(descriptor, 0, classNames).forEach {
                table.classes.add(table.tableClasses.named(it))
              }
            1 -> decodeSerializableElement(descriptor, 1, EntryList)
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unexpected object table element $index")
          }
        }
      }
      return table
    }
  }

  /** The entries, appended to the current table one by one so that later ones can refer to them. */
  private object EntryList : KSerializer<Unit> {
    private val list = ListSerializer(EntrySerializer)
    override val descriptor: SerialDescriptor = list.descriptor

    override fun serialize(encoder: Encoder, value: Unit) = error("Written as a list")

    override fun deserialize(decoder: Decoder) {
      val table = current()
      decoder.decodeStructure(descriptor) {
        if (decodeSequentially()) {
          repeat(decodeCollectionSize(descriptor)) {
            table.values.add(decodeSerializableElement(descriptor, it, EntrySerializer))
          }
        } else {
          while (true) {
            val index = decodeElementIndex(descriptor)
            if (index == CompositeDecoder.DECODE_DONE) break
            table.values.add(decodeSerializableElement(descriptor, index, EntrySerializer))
          }
        }
      }
    }
  }

  companion object {

    private val current = ThreadLocal<ObjectTable>()

    fun current(): ObjectTable =
      current.get() ?: error("Reference serializers can only be used within an object table")

    /** Types are values, so equal ones share an entry. */
    val TYPES_BY_EQUALITY: (Any) -> Any? = { it as? Type }

    /**
     * A table to encode objects of [tableClasses] into. Objects with equal [internKey]s share an
     * entry; a null key interns by identity.
     */
    fun forEncoding(
      module: SerializersModule,
      tableClasses: TableClasses,
      internKey: (Any) -> Any? = TYPES_BY_EQUALITY,
      ambient: List<Any> = listOf(),
    ) = ObjectTable(module, tableClasses, internKey, ambient, collecting = true)

    fun forDecoding(
      module: SerializersModule,
      tableClasses: TableClasses,
      ambient: List<Any> = listOf(),
    ) = ObjectTable(module, tableClasses, { null }, ambient, collecting = false)

    /** Runs [block] with this table as the one the reference serializers use. */
    fun <T> ObjectTable.use(block: () -> T): T {
      check(current.get() == null) { "Nested object tables are not supported" }
      current.set(this)
      try {
        return block()
      } finally {
        current.remove()
      }
    }
  }
}

/** Records what a serializer writes, as an equality key. */
@OptIn(ExperimentalSerializationApi::class)
private class KeyEncoder(override val serializersModule: SerializersModule) : AbstractEncoder() {
  val key = ArrayList<Any?>()

  override fun encodeValue(value: Any) {
    key.add(value)
  }

  override fun encodeNull() {
    key.add(null)
  }

  override fun encodeElement(descriptor: SerialDescriptor, index: Int): Boolean {
    key.add(index)
    return true
  }

  override fun beginStructure(descriptor: SerialDescriptor): CompositeEncoder {
    key.add(descriptor.serialName)
    return this
  }

  override fun endStructure(descriptor: SerialDescriptor) {
    key.add(Unit)
  }
}

/** Runs serializers without producing output: the first encoding pass. */
@OptIn(ExperimentalSerializationApi::class)
class CollectingEncoder(override val serializersModule: SerializersModule) : AbstractEncoder() {
  override fun encodeValue(value: Any) {}

  override fun encodeNull() {}
}
