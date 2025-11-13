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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.xcfa.model.*

/**
 * Removes atomic begin and end labels that enclose an atomic block within a single edge. It is
 * assumed that atomic blocks are well-formed (atomic begins and ends are properly paired: e.g., no
 * atomic_begin, atomic_begin, atomic_end where the first atomic_begin is on an earlier edge).
 *
 * Note: AtomicBeginLabels are (mostly) all equal, as are AtomicEndLabels. Therefore, identity
 * comparison (===) is used to distinguish between different instances.
 */
class RemoveUnnecessaryAtomicBlocksPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      val labelsToRemove = mutableListOf<AtomicFenceLabel>()
      edge.collect(::collectAtomicBegins, labelsToRemove)
      edge.collect(::collectAtomicEnds, labelsToRemove)

      if (labelsToRemove.isNotEmpty()) {
        val newLabel = edge.label.removeLabels(labelsToRemove)
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  private fun XcfaLabel.removeLabels(toRemove: Collection<XcfaLabel>): XcfaLabel =
    when {
      toRemove.any { it === this } -> NopLabel
      this is SequenceLabel ->
        SequenceLabel(labels.map { it.removeLabels(toRemove) }.filter { it !is NopLabel })
      this is NondetLabel ->
        NondetLabel(labels.map { it.removeLabels(toRemove) }.filter { it !is NopLabel }.toSet())
      else -> this
    }

  private fun <T> XcfaEdge.collect(
    collector: (XcfaLabel, MutableList<T>, MutableList<T>) -> Unit,
    collection: MutableList<in T>,
  ) {
    val allItems = mutableListOf<T>()
    val openItems = mutableListOf<T>()
    collector(label, allItems, openItems)
    val collected = allItems.filter { a -> openItems.none { it === a } }
    collection.addAll(collected)
  }

  private fun collectAtomicBegins(
    label: XcfaLabel,
    allAtomicBegins: MutableList<AtomicBeginLabel>,
    openAtomicBegins: MutableList<AtomicBeginLabel>,
  ) {
    when (label) {
      is AtomicBeginLabel -> {
        allAtomicBegins.add(label)
        openAtomicBegins.add(label)
      }
      is AtomicEndLabel -> {
        openAtomicBegins.clear()
      }
      is SequenceLabel -> {
        label.labels.forEach { collectAtomicBegins(it, allAtomicBegins, openAtomicBegins) }
      }
      is NondetLabel -> {
        val allOab = mutableListOf<AtomicBeginLabel>()
        label.labels.map {
          val oab = openAtomicBegins.toMutableList()
          collectAtomicBegins(it, allAtomicBegins, oab)
          allOab.addAll(oab)
        }
        openAtomicBegins.clear()
        openAtomicBegins.addAll(allOab)
      }
      else -> {}
    }
  }

  private fun collectAtomicEnds(
    label: XcfaLabel,
    allAtomicEnds: MutableList<AtomicEndLabel>,
    openAtomicEnds: MutableList<AtomicEndLabel>,
  ) {
    when (label) {
      is AtomicBeginLabel -> {
        openAtomicEnds.clear()
      }
      is AtomicEndLabel -> {
        allAtomicEnds.add(label)
        openAtomicEnds.add(label)
      }
      is SequenceLabel -> {
        label.labels.reversed().forEach { collectAtomicEnds(it, allAtomicEnds, openAtomicEnds) }
      }
      is NondetLabel -> {
        val allOae = mutableListOf<AtomicEndLabel>()
        label.labels.map {
          val oae = openAtomicEnds.toMutableList()
          collectAtomicEnds(it, allAtomicEnds, oae)
          allOae.addAll(oae)
        }
        openAtomicEnds.clear()
        openAtomicEnds.addAll(allOae)
      }
      else -> {}
    }
  }
}
