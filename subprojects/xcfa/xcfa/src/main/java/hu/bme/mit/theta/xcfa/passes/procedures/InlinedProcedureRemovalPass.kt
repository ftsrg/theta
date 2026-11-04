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
package hu.bme.mit.theta.xcfa.passes.procedures

import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.recordRemovedLocation
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/** Removes procedures that are not used anymore. */
class InlinedProcedureRemovalPass(private val parseContext: ParseContext? = null) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder in builder.parent.getInitProcedures().map { it.first }) return builder

    if (builder.name !in calledNames(builder)) {
      parseContext?.let { context ->
        builder
          .getLocs()
          .filter { it.metadata.keepsLocation() }
          .forEach { context.recordRemovedLocation(it, False()) }
      }
      builder.parent.removeProcedure(builder)
    }
    return builder
  }

  /** Scanned once per phase, as every procedure asks and a program can have thousands of them. */
  private fun calledNames(builder: XcfaProcedureBuilder): Set<String> {
    val phase = builder.currentPhase
    @Suppress("UNCHECKED_CAST")
    val cached = builder.parent.metaData[CALLED_NAMES] as? Pair<Int, Set<String>>
    if (cached != null && cached.first == phase) return cached.second
    val names = LinkedHashSet<String>()
    builder.parent.getProcedures().forEach { proc ->
      proc.getEdges().forEach { edge ->
        edge.getFlatLabels().forEach { label ->
          if (label is InvokeLabel) names.add(label.name)
          if (label is StartLabel) names.add(label.name)
        }
      }
    }
    builder.parent.metaData[CALLED_NAMES] = phase to names
    return names
  }
}

private const val CALLED_NAMES = "inlinedProcedureRemovalCalledNames"
