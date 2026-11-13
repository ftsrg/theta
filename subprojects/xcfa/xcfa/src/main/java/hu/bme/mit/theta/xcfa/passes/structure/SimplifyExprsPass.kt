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
package hu.bme.mit.theta.xcfa.passes.structure

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.getInitLoops
import hu.bme.mit.theta.xcfa.utils.getNonConcurrentEdges
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.mergeIncomingValuations
import hu.bme.mit.theta.xcfa.utils.recordPassInvariants
import hu.bme.mit.theta.xcfa.utils.simplify

/**
 * This pass simplifies the expressions inside statements and substitutes the values of constant
 * variables (that is, variables assigned only once). Requires the ProcedureBuilder to be
 * `deterministic` (@see DeterministicPass) Sets the `simplifiedExprs` flag on the ProcedureBuilder
 */
private const val MAX_PATHS = 4

class SimplifyExprsPass(
  val parseContext: ParseContext,
  val property: XcfaProperty? = null,
  private val recordPassInvariants: Boolean = false,
) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (property?.verifiedProperty?.equals(ErrorDetection.OVERFLOW) ?: false) {
      return builder
    }
    checkNotNull(builder.metaData["deterministic"])
    val unusedLocRemovalPass = UnusedLocRemovalPass()
    var edges = LinkedHashSet(builder.getEdges())
    val isInitProcedure = builder in builder.parent.getInitProcedures().map { it.first }
    // without threads nothing runs concurrently with the entry procedure: its globals change only
    // through its own edges and calls (which still clear them below)
    val singleThreaded =
      builder.parent.getProcedures().none { proc ->
        proc.getEdges().any { e -> e.getFlatLabels().any { it is StartLabel } }
      }
    val initEdges =
      LinkedHashSet(
        if (isInitProcedure) getNonConcurrentEdges(builder.parent, true).first else emptySet()
      )
    val initLoops = getInitLoops(builder.initLoc, initEdges)

    val valuations = LinkedHashMap<XcfaEdge, Valuation>()
    val pathValuations = LinkedHashMap<XcfaEdge, List<Valuation>>()
    val constValuation = MutableValuation()
    val globalVars = builder.parent.getVars()
    val preserveSharedAccesses = property?.inputProperty == ErrorDetection.DATA_RACE
    val modifiedGlobals = mutableListOf<VarDecl<*>>()
    builder.parent
      .getVars()
      .map { it.wrappedVar }
      .getConstAndModifiedVars(builder.parent.getProcedures(), constValuation, modifiedGlobals)

    builder.getVars().getConstAndModifiedVars(setOf(builder), constValuation)

    lateinit var lastEdges: LinkedHashSet<XcfaEdge>
    do {
      lastEdges = edges

      val toVisit = builder.initLoc.outgoingEdges.toMutableSet()
      val visited = mutableSetOf<XcfaEdge>()
      while (toVisit.isNotEmpty()) {
        val edge =
          toVisit.find { candidate -> candidate.source.incomingEdges.all { it in visited } }
            ?: toVisit.first()
        toVisit.remove(edge)
        visited.add(edge)
        val incomingValuations = mergeIncomingValuations(edge.source, valuations, initLoops)
        val localValuation = MutableValuation.copyOf(incomingValuations)
        localValuation.putAll(constValuation)
        val localPaths =
          mergeIncomingPaths(edge.source, valuations, pathValuations, initLoops).map {
            MutableValuation.copyOf(it).apply { putAll(constValuation) }
          }

        val oldLabels = edge.getFlatLabels()
        val feasiblePaths = localPaths.toMutableList()
        val newLabels =
          oldLabels.map { old ->
            val new = old.simplify(localValuation, parseContext)
            // each path takes the label too; one an assume contradicts is dropped, and once a
            // single path is left, the rest of the edge is simplified with its constants
            feasiblePaths.removeIf { path ->
              old.simplify(path, parseContext).let { (it as? StmtLabel)?.stmt == Assume(False()) }
            }
            if (old is InvokeLabel) {
              old
                .collectVarsWithAccessType()
                .filterValues { it.isWritten }
                .forEach { (outArg, _) ->
                  localValuation.remove(outArg)
                  feasiblePaths.forEach { it.remove(outArg) }
                }
            }
            if (old.isAssume) feasiblePaths.singleOrNull()?.let { localValuation.putAll(it) }
            if (preserveSharedAccesses && old.isAssume && dropsSharedAccess(old, new, globalVars)) {
              old
            } else {
              new
            }
          }

        val nonConcurrent = edge in initEdges || (isInitProcedure && singleThreaded)
        if (!nonConcurrent || newLabels.any { it is InvokeLabel || it is StartLabel }) {
          // note that global variable values are still propagated within an edge (XcfaEdge is
          // considered atomic)
          modifiedGlobals.forEach { v ->
            localValuation.remove(v)
            feasiblePaths.forEach { it.remove(v) }
          }
        }

        if (newLabels != oldLabels) {
          builder.removeEdge(edge)
          valuations.remove(edge)
          pathValuations.remove(edge)
          if (newLabels.firstOrNull().let { (it as? StmtLabel)?.stmt != Assume(False()) }) {
            val newEdge = edge.withLabel(SequenceLabel(newLabels))
            builder.addEdge(newEdge)
            visited.add(newEdge)
            valuations[newEdge] = localValuation
            pathValuations[newEdge] = feasiblePaths
          }
        } else {
          valuations[edge] = localValuation
          pathValuations[edge] = feasiblePaths
        }

        toVisit.addAll(edge.target.outgoingEdges.filter { it !in visited })
      }
      unusedLocRemovalPass.runChecked(builder)

      edges = LinkedHashSet(builder.getEdges())
    } while (lastEdges != edges)
    builder.metaData["simplifiedExprs"] = Unit
    if (recordPassInvariants)
      valuations
        .map { (edge, valuation) ->
          edge.target to
            ImmutableValuation.from(valuation.toMap() - constValuation.toMap().keys).toExpr()
        }
        .groupBy { it.first }
        .forEach { (location, invariants) ->
          parseContext.recordPassInvariants(location, BoolExprs.Or(invariants.map { it.second }))
        }
    return builder
  }

  /**
   * The valuations of the (at most [MAX_PATHS]) paths reaching [loc], kept apart where the merge
   * would lose a constant on which they differ: e.g. a failed allocation leaves the pointer NULL
   * and the allocator's ghost state untouched, and the program's own NULL check then selects the
   * path on which all of them are constants again. Empty when unknown (loops, unvisited edges).
   */
  private fun mergeIncomingPaths(
    loc: XcfaLocation,
    valuations: Map<XcfaEdge, Valuation>,
    pathValuations: Map<XcfaEdge, List<Valuation>>,
    initLoops: Map<XcfaLocation, Set<XcfaEdge>>,
  ): List<Valuation> {
    val incoming =
      loc.incomingEdges.filter {
        it.getFlatLabels().none { l -> l is StmtLabel && l.stmt == Assume(False()) }
      }
    if (loc in initLoops || incoming.isEmpty() || incoming.any { it !in valuations })
      return listOf()
    val paths =
      incoming.flatMap { e ->
        pathValuations[e]?.takeIf { it.isNotEmpty() } ?: listOf(valuations[e]!!)
      }
    val distinct = paths.distinctBy { it.toMap() }
    return if (distinct.size <= MAX_PATHS) distinct else listOf()
  }

  private val XcfaLabel.isAssume: Boolean
    get() = this is StmtLabel && stmt is AssumeStmt

  /**
   * Whether simplifying the assume [old] into [new] would erase an access to shared memory.
   *
   * Folding a branch condition drops whole subexpressions -- `(a == 0 && b == 0) || 1` becomes
   * `true` -- and with them the reads they contained. That is sound for reachability, but for a
   * data race those erased reads are exactly the accesses that would have raced: the conflicting
   * access simply stops existing, so the race is reported as absent (`reorder_c11_good-*`).
   *
   * Only assumes are guarded. Simplification also *rewrites* the address expression of a
   * dereference -- folding `base + offset` to a constant -- and an assignment relies on that, since
   * it is what lets the atomic-cell check resolve the object base (`09atomicfield_norace`). Such a
   * rewrite drops the global var and the original dereference from the label without dropping the
   * access, so a plain access comparison cannot tell the two apart.
   */
  private fun dropsSharedAccess(
    old: XcfaLabel,
    new: XcfaLabel,
    globalVars: Set<XcfaGlobalVar>,
  ): Boolean {
    fun nonAtomicGlobals(label: XcfaLabel) =
      label.collectVarsWithAccessType().filterKeys {
        globalVars.any { v -> v.wrappedVar == it && !v.atomic }
      }

    fun derefCount(label: XcfaLabel) = label.dereferencesWithAccessType.size

    val oldGlobals = nonAtomicGlobals(old)
    val newGlobals = nonAtomicGlobals(new)
    val lostGlobal =
      oldGlobals.any { (v, access) ->
        val kept = newGlobals[v]
        (access.isRead && !kept.isRead) || (access.isWritten && !kept.isWritten)
      }
    return lostGlobal || derefCount(new) < derefCount(old)
  }

  /**
   * Separates the variables in this collection. The constant variables are added to the given
   * valuation with their values. Modified variables are returned as a list.
   */
  private fun Collection<VarDecl<*>>.getConstAndModifiedVars(
    accessingProcedures: Set<XcfaProcedureBuilder>,
    constValuation: MutableValuation,
    modifiedVariables: MutableList<VarDecl<*>> = mutableListOf(),
  ) {
    val writeCounts = associateWith { 0 }.toMutableMap()
    val writes = mutableMapOf<VarDecl<*>, XcfaLabel>()
    accessingProcedures.forEach { proc ->
      val toVisit = mutableListOf(proc.initLoc)
      val visited = mutableSetOf<XcfaLocation>()
      while (toVisit.isNotEmpty()) {
        val loc = toVisit.removeFirst()
        if (!visited.add(loc)) continue
        loc.outgoingEdges.forEach { edge ->
          edge.getFlatLabels().forEach { label ->
            label.collectVarsWithAccessType().forEach { (v, access) ->
              if (v in writeCounts) {
                // explicit write or range assume for uninitialized local vars
                if (
                  access.isWritten ||
                    (access.isRead && accessingProcedures.size == 1 && writeCounts[v] == 0)
                ) {
                  writeCounts[v] = writeCounts[v]!! + 1
                  writes.putIfAbsent(v, label)
                }
              }
            }
          }
          toVisit.add(edge.target)
        }
      }
    }

    val potentialConsts =
      filter { v ->
          if (writeCounts[v]!! > 1) {
            modifiedVariables.add(v)
            false
          } else {
            true
          }
        }
        .toMutableSet()

    do {
      var changed = false
      potentialConsts.removeIf { v ->
        writes[v]?.let { write ->
          val valuation = MutableValuation.copyOf(constValuation)
          write.simplify(valuation, parseContext)
          valuation.toMap()[v]?.let {
            if (v !in constValuation.decls) {
              constValuation.put(v, it)
              changed = true
            }
            true // remove if we have a constant value for it
          } ?: false // we may have a chance later: e.g., x := y if y gets a value
        } ?: true // no writing label found for v -> remove
      }
    } while (changed) // no change, no point in iterating further
  }
}
