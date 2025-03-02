/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.oc

private sealed interface IArray<T> {
  operator fun get(index: Int): T

  operator fun set(index: Int, value: T)

  fun withIndex(): Iterable<IndexedValue<T>>
}

sealed class GlobalRelationBase<T>(private val relation: Array<out IArray<T>>) {

  val size
    get() = relation.size

  operator fun get(from: Int, to: Int): T = relation[from][to]

  operator fun set(from: Int, to: Int, value: T) {
    relation[from][to] = value
  }

  fun forEachPair(action: (Int, Int, T) -> Unit) {
    for ((i, row) in relation.withIndex()) {
      for ((j, value) in row.withIndex()) {
        action(i, j, value)
      }
    }
  }

  abstract fun copy(): GlobalRelationBase<T>

  protected abstract fun isRelated(value: T): Boolean

  protected abstract fun combine(value1: T, value2: T): T

  fun closeNoCycle(initials: List<Triple<Int, Int, T>>) {
    check(close(initials) == null) { "Self-loop not allowed." }
  }

  fun close(from: Int, to: Int, value: T) = close(listOf(Triple(from, to, value)))

  fun close(initials: List<Triple<Int, Int, T>>): T? {
    for ((from, to, value) in initials) {
      if (from == to) return value
    }
    val toClose = initials.toMutableList()
    while (toClose.isNotEmpty()) {
      val (from, to, value) = toClose.removeFirst()
      check(from != to)
      if (isRelated(relation[from][to])) continue

      relation[from][to] = value
      for ((other, otherValue) in relation[to].withIndex()) {
        if (isRelated(otherValue) && !isRelated(relation[from][other])) {
          // to -> other, not from -> other
          val combined = combine(value, otherValue)
          if (from == other) return combined // cycle (self-loop) found
          toClose.add(Triple(from, other, combined))
        }
      }
      for ((other, otherValues) in relation.withIndex()) {
        if (isRelated(otherValues[from]) && !isRelated(relation[other][to])) {
          // other -> from, not other -> to
          val combined = combine(value, otherValues[from])
          if (other == to) return combined // cycle (self-loop) found
          toClose.add(Triple(other, to, combined))
        }
      }
    }
    return null
  }
}

private class GenericArrayHolder<T>(private val array: Array<T>) : IArray<T> {
  override fun get(index: Int) = array[index]

  override fun withIndex() = array.withIndex()

  override fun set(index: Int, value: T) = array.set(index, value)
}

private class BooleanArrayHolder(private val array: BooleanArray) : IArray<Boolean> {
  override fun get(index: Int) = array[index]

  override fun withIndex() = array.withIndex()

  override fun set(index: Int, value: Boolean) = array.set(index, value)
}

class GlobalRelation(size: Int, default: (Pair<Int, Int>) -> Reason?) :
  GlobalRelationBase<Reason?>(
    Array(size) { i -> GenericArrayHolder(Array(size) { j -> default(i to j) }) }
  ) {

  override fun copy() = GlobalRelation(size) { (i, j) -> this[i, j] }

  override fun isRelated(value: Reason?) = value != null

  override fun combine(value1: Reason?, value2: Reason?) = value1!! and value2!!
}

class BooleanGlobalRelation(size: Int, default: (Pair<Int, Int>) -> Boolean) :
  GlobalRelationBase<Boolean>(
    Array(size) { i -> BooleanArrayHolder(BooleanArray(size) { j -> default(i to j) }) }
  ) {

  override fun copy() = BooleanGlobalRelation(size) { (i, j) -> this[i, j] }

  override fun isRelated(value: Boolean) = value

  override fun combine(value1: Boolean, value2: Boolean) = value1 || value2
}
