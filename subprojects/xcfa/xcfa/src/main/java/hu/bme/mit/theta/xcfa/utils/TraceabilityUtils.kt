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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.containsTraceability
import hu.bme.mit.theta.core.type.stripTraceability
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

/**
 * This XCFA with the traceability info (e.g. C types) removed from its expressions; itself if it
 * has none. Analyses take this form: they match on expression classes, which a wrapper would hide.
 * The copy's locations and edges are equal to the originals, so its traces can be looked up in
 * either.
 */
fun XCFA.withoutTraceability(): XCFA {
  val traced =
    procedures.any { p ->
      p.prop.containsTraceability() || p.edges.any { it.label.withoutTraceability() !== it.label }
    } || initProcedures.any { (_, params) -> params.any { it.containsTraceability() } }
  if (!traced) return this
  val builder = XcfaBuilder(name, globalVars.toMutableSet())
  val passes = ProcedurePassManager(listOf(StripTraceabilityPass))
  procedures.forEach { builder.addProcedure(it.deepCopy(passes, unsafeUnrollUsed)) }
  initProcedures.forEach { (proc, params) ->
    val initProc =
      builder.getProcedures().find { it.name == proc.name }
        ?: proc.deepCopy(passes, unsafeUnrollUsed)
    builder.addEntryPoint(initProc, params.map { it.bare() })
  }
  return builder.build().also { it.unsafeUnrollUsed = unsafeUnrollUsed }
}

/** This label with the traceability info removed from its expressions; itself if it has none. */
fun XcfaLabel.withoutTraceability(): XcfaLabel =
  when (this) {
    is StmtLabel -> stmt.stripTraceability().let { if (it === stmt) this else copy(stmt = it) }
    is InvokeLabel -> params.stripEach()?.let { copy(params = it) } ?: this
    is StartLabel -> params.stripEach()?.let { copy(params = it) } ?: this
    is ReturnLabel ->
      enclosedLabel.withoutTraceability().let {
        if (it === enclosedLabel) this else ReturnLabel(it)
      }
    is SequenceLabel -> {
      val stripped = labels.map { it.withoutTraceability() }
      if (stripped.indices.all { stripped[it] === labels[it] }) this else copy(labels = stripped)
    }
    is NondetLabel -> {
      val stripped = labels.map { it.withoutTraceability() }
      if (stripped.zip(labels).all { (a, b) -> a === b }) this else copy(labels = stripped.toSet())
    }
    is FenceLabel -> lock.bare().let { if (it === lock) this else withLock(it) }
    is JoinLabel,
    NopLabel -> this
  }

private object StripTraceabilityPass : ProcedurePass {
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.prop = builder.prop.bare()
    for (edge in builder.getEdges().toList()) {
      val label = edge.label.withoutTraceability()
      if (label !== edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(label))
      }
    }
    return builder
  }
}

private fun <T : hu.bme.mit.theta.core.type.Type> Expr<T>.bare(): Expr<T> =
  if (containsTraceability()) stripTraceability() else this

private fun List<Expr<*>>.stripEach(): List<Expr<*>>? {
  val stripped = map { it.bare() }
  return if (stripped.indices.all { stripped[it] === this[it] }) null else stripped
}
