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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import java.util.*

@DslMarker annotation class XcfaDsl

@XcfaDsl
class XcfaBuilder
@JvmOverloads
constructor(var name: String, private val vars: MutableSet<XcfaGlobalVar> = LinkedHashSet()) {

  private val procedures: MutableSet<XcfaProcedureBuilder> = LinkedHashSet()
  private val initProcedures: MutableList<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = ArrayList()
  val metaData: MutableMap<String, Any> = LinkedHashMap()

  fun getVars(): Set<XcfaGlobalVar> = vars

  fun getProcedures(): Set<XcfaProcedureBuilder> = procedures

  fun getInitProcedures(): List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = initProcedures

  fun build(): XCFA {
    return XCFA(
      name = name,
      globalVars = vars,
      procedureBuilders = procedures,
      initProcedureBuilders = initProcedures,
    )
  }

  fun addVar(toAdd: XcfaGlobalVar) {
    vars.add(toAdd)
  }

  fun addProcedure(toAdd: XcfaProcedureBuilder) {
    procedures.add(toAdd)
    toAdd.parent = this
  }

  fun addEntryPoint(toAdd: XcfaProcedureBuilder, params: List<Expr<*>>) {
    addProcedure(toAdd)
    initProcedures.add(Pair(toAdd, params))
  }

  fun removeProcedure(toRemove: XcfaProcedureBuilder) {
    check(!initProcedures.any { it.first == toRemove }) {
      "Cannot remove an entry point procedure!"
    }
    procedures.remove(toRemove)
  }
}

@XcfaDsl
class XcfaProcedureBuilder
@JvmOverloads
constructor(
  var name: String,
  val manager: ProcedurePassManager,
  private val params: MutableList<Pair<VarDecl<*>, ParamDirection>> = ArrayList(),
  private val vars: MutableSet<VarDecl<*>> = LinkedHashSet(),
  private val atomicVars: MutableSet<VarDecl<*>> = LinkedHashSet(),
  private val locs: MutableSet<XcfaLocation> = LinkedHashSet(),
  private val edges: MutableSet<XcfaEdge> = LinkedHashSet(),
  val metaData: MutableMap<String, Any> = LinkedHashMap(),
  unsafeUnrollUsed: Boolean = false,
  var prop: Expr<BoolType> = True(),
) {

  lateinit var initLoc: XcfaLocation
    private set

  var finalLoc: Optional<XcfaLocation> = Optional.empty()
    private set

  var errorLoc: Optional<XcfaLocation> = Optional.empty()
    private set

  var unsafeUnrollUsed: Boolean = unsafeUnrollUsed
    private set

  lateinit var parent: XcfaBuilder
  private lateinit var built: XcfaProcedure
  private lateinit var optimized: XcfaProcedureBuilder
  private lateinit var partlyOptimized: XcfaProcedureBuilder
  private var lastOptimized: Int = -1

  fun getParams(): List<Pair<VarDecl<*>, ParamDirection>> =
    when {
      this::optimized.isInitialized -> optimized.params
      this::partlyOptimized.isInitialized -> partlyOptimized.params
      else -> params
    }

  fun getVars(): Set<VarDecl<*>> =
    when {
      this::optimized.isInitialized -> optimized.vars
      this::partlyOptimized.isInitialized -> partlyOptimized.vars
      else -> vars
    }

  fun getLocs(): Set<XcfaLocation> =
    when {
      this::optimized.isInitialized -> optimized.locs
      this::partlyOptimized.isInitialized -> partlyOptimized.locs
      else -> locs
    }

  fun getEdges(): Set<XcfaEdge> =
    when {
      this::optimized.isInitialized -> optimized.edges
      this::partlyOptimized.isInitialized -> partlyOptimized.edges
      else -> edges
    }

  fun optimize() {
    if (!this::optimized.isInitialized) {
      var that = this
      for (pass in manager.passes.flatten()) {
        that = pass.run(that)
      }
      optimized = that
    }
  }

  fun optimize(
    phase: Int
  ): Boolean { // true, if optimization is finished (no more phases to execute)
    if (this::optimized.isInitialized || phase >= manager.passes.size) return true
    if (phase <= lastOptimized) return lastOptimized >= manager.passes.size - 1
    check(phase == lastOptimized + 1) { "Wrong optimization phase!" }

    var that = if (this::partlyOptimized.isInitialized) partlyOptimized else this
    for (pass in manager.passes[phase]) {
      that = pass.run(that)
      that.checkEdgesHaveLocations(pass)
    }

    partlyOptimized = that
    lastOptimized = phase
    if (phase >= manager.passes.size - 1) optimized = that
    return phase >= manager.passes.size - 1
  }

  fun build(parent: XCFA): XcfaProcedure {
    if (this::built.isInitialized) return built
    if (!this::optimized.isInitialized) optimize()
    built =
      XcfaProcedure(
        name = optimized.name,
        params = optimized.params,
        vars = optimized.vars,
        locs = optimized.locs,
        edges = optimized.edges,
        initLoc = optimized.initLoc,
        finalLoc = optimized.finalLoc,
        errorLoc = optimized.errorLoc,
        prop = prop,
      )
    built.parent = parent
    return built
  }

  fun addParam(toAdd: VarDecl<*>, dir: ParamDirection) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    params.add(Pair(toAdd, dir))
    vars.add(toAdd)
  }

  fun addVar(toAdd: VarDecl<*>) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    vars.add(toAdd)
  }

  fun setAtomic(v: VarDecl<*>) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove/modify elements after optimization passes!"
    }
    atomicVars.add(v)
  }

  fun removeVar(toRemove: VarDecl<*>) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    vars.remove(toRemove)
  }

  @JvmOverloads
  fun createErrorLoc(metaData: MetaData = EmptyMetaData) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    if (errorLoc.isEmpty) {
      errorLoc = Optional.of(XcfaLocation(name + "_error", error = true, metadata = metaData))
      locs.add(errorLoc.get())
    }
  }

  @JvmOverloads
  fun createFinalLoc(metaData: MetaData = EmptyMetaData) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    if (finalLoc.isEmpty) {
      finalLoc = Optional.of(XcfaLocation(name + "_final", final = true, metadata = metaData))
      locs.add(finalLoc.get())
    }
  }

  @JvmOverloads
  fun createInitLoc(metaData: MetaData = EmptyMetaData) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    if (!this::initLoc.isInitialized) {
      initLoc = XcfaLocation(name + "_init", initial = true, metadata = metaData)
      locs.add(initLoc)
    }
  }

  fun copyMetaLocs(
    initLoc: XcfaLocation,
    finalLoc: Optional<XcfaLocation>,
    errorLoc: Optional<XcfaLocation>,
  ) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    this.initLoc = initLoc
    this.finalLoc = finalLoc
    this.errorLoc = errorLoc
  }

  fun addEdge(toAdd: XcfaEdge) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    addLoc(toAdd.source)
    addLoc(toAdd.target)
    // addLoc is a no-op for a location that is already known, and refuses to (re-)add an error,
    // initial or final one -- so an edge can still end up attached to a location this procedure
    // does not list, which every consumer that maps edges through `locs` (XcfaProcedure.deepCopy,
    // most directly) will then fail on with a bare NullPointerException far from the cause.
    check(toAdd.source in locs && toAdd.target in locs) {
      "Edge ${toAdd.source.name} -> ${toAdd.target.name} added to procedure $name with" +
        " an endpoint that is not one of its locations" +
        " (source present: ${toAdd.source in locs}, target present: ${toAdd.target in locs})"
    }
    edges.add(toAdd)
    toAdd.source.outgoingEdges.add(toAdd)
    toAdd.target.incomingEdges.add(toAdd)
  }

  fun addLoc(toAdd: XcfaLocation) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    if (!locs.contains(toAdd)) {
      check(!toAdd.error)
      check(!toAdd.initial)
      check(!toAdd.final)
      locs.add(toAdd)
    }
  }

  /**
   * Asserts the basic well-formedness every consumer assumes: each edge runs between two locations
   * this procedure actually lists.
   *
   * [removeLoc] drops a location without touching the edges attached to it, so a pass that removes
   * locations and edges in the wrong order -- or misses an edge coming in from outside the region
   * it is rewriting -- leaves the two out of sync. Nothing notices until something maps the edges
   * through `locs` much later (`XcfaProcedure.deepCopy` does, and dies on a `!!` with no indication
   * of which pass broke it), so the check is done here, right after the pass that could have caused
   * it, and names that pass.
   */
  private fun checkEdgesHaveLocations(pass: ProcedurePass) {
    // Identity, not equality. XcfaLocation is a data class, so a *different instance* carrying the
    // same name/flags/metadata compares equal and satisfies `in locs` -- while owning its own,
    // separate incoming/outgoing sets. An edge attached to such a stray twin is invisible to every
    // traversal that walks adjacency (which is all of them, including LoopUnrollPass's back-edge
    // cut), yet XcfaProcedure.deepCopy resolves endpoints through a map keyed by equality and so
    // silently re-points the edge onto the registered instance. A cycle hidden that way only
    // materialises in the copy, where it surfaces as the OC checker rejecting the task for "loops".
    val registered = java.util.Collections.newSetFromMap(java.util.IdentityHashMap<XcfaLocation, Boolean>())
    registered.addAll(locs)
    val dangling = edges.filter { it.source !in registered || it.target !in registered }
    check(dangling.isEmpty()) {
      "${pass::class.simpleName} left ${dangling.size} edge(s) of procedure $name attached to" +
        " locations it no longer contains: " +
        dangling.take(5).joinToString {
          "${it.source.name}${if (it.source in locs) "" else "(missing)"} ->" +
            " ${it.target.name}${if (it.target in locs) "" else "(missing)"}"
        }
    }
  }

  fun removeEdge(toRemove: XcfaEdge) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    check(
      toRemove.source.outgoingEdges.contains(toRemove) &&
        toRemove.target.incomingEdges.contains(toRemove) &&
        edges.contains(toRemove)
    ) {
      "Cannot remove edge if it wasn't already present!"
    }
    toRemove.source.outgoingEdges.remove(toRemove)
    toRemove.target.incomingEdges.remove(toRemove)
    edges.remove(toRemove)
  }

  fun removeLoc(toRemove: XcfaLocation) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    locs.remove(toRemove)
    if (toRemove.error) {
      errorLoc = Optional.empty()
    }
  }

  fun removeLocs(pred: (XcfaLocation) -> Boolean) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    while (true) {
      // Snapshot the matches instead of re-evaluating `pred` while edges are being unhooked: the
      // usual predicate asks whether a location has incoming edges, so removing edges underneath it
      // changes the answer mid-pass. That is how a location could leave `locs` while an edge still
      // pointed at it, leaving the builder with an edge attached to a location it no longer holds.
      val toRemove = locs.filterTo(LinkedHashSet(), pred)
      if (toRemove.isEmpty()) break
      locs.removeAll(toRemove)
      // An edge whose *target* vanished is just as orphaned as one whose source did, so drop
      // everything incident to a removed location and unhook it from the endpoint that survives.
      edges.removeIf { edge ->
        (edge.source in toRemove || edge.target in toRemove).also { removing ->
          if (removing) {
            edge.source.outgoingEdges.remove(edge)
            edge.target.incomingEdges.remove(edge)
          }
        }
      }
    }
  }

  fun changeVars(varLut: Map<VarDecl<*>, VarDecl<*>>) {
    check(!this::optimized.isInitialized) {
      "Cannot add/remove new elements after optimization passes!"
    }
    val savedVars = ArrayList(vars)
    vars.clear()
    savedVars.forEach { vars.add(checkNotNull(varLut[it])) }
    val savedParams = ArrayList(params)
    params.clear()
    savedParams.forEach { params.add(Pair(checkNotNull(varLut[it.first]), it.second)) }
  }

  fun setUnsafeUnroll() {
    unsafeUnrollUsed = true
  }

  override fun toString(): String = name
}
