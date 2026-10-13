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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.references

/**
 * A flat record of what a program looks like, emitted once per parse as a single JSON line.
 *
 * This exists to be *mined*, not read: it is the raw material for deciding which program properties
 * actually predict which algorithm wins, so it errs towards recording too much. Everything here is
 * derived from the structure of the XCFA and the frontend's own type information -- no identifier
 * from the input program is read, so nothing here can encode "which benchmark is this".
 */
fun xcfaTraits(
  xcfa: XCFA,
  parseContext: ParseContext,
  property: String,
  propertyFile: String,
): String {
  val procs = xcfa.procedures.toList()
  val edges = procs.flatMap { it.edges }
  val locs = procs.flatMap { it.locs }
  val labels = edges.flatMap { it.label.getFlatLabels() }
  val stmts = labels.mapNotNull { (it as? StmtLabel)?.stmt }

  // --- control flow ------------------------------------------------------------------------
  val backEdges = procs.sumOf { it.backEdgeCount() }
  val cyclicProcs = procs.count { it.backEdgeCount() > 0 }
  // McCabe, summed over procedures: E - N + 2 for each.
  val cyclomatic = procs.sumOf { maxOf(0, it.edges.size - it.locs.size + 2) }
  val maxCyclomatic = procs.maxOfOrNull { maxOf(0, it.edges.size - it.locs.size + 2) } ?: 0
  val branching = locs.count { it.outgoingEdges.size > 1 }

  // --- variables and SMT types -------------------------------------------------------------
  val allVars: List<VarDecl<*>> =
    (xcfa.globalVars.map { it.wrappedVar } + procs.flatMap { it.vars })
  val typeNames = allVars.map { it.type.smtName() }
  val bvWidths = allVars.mapNotNull { (it.type as? BvType)?.size }.distinct().sorted()

  // --- memory ------------------------------------------------------------------------------
  val derefs = labels.flatMap { it.dereferencesWithAccessType.entries }
  val derefReads = derefs.count { it.value.isRead }
  val derefWrites = derefs.count { it.value.isWritten }
  val constOffsets = derefs.count { it.key.offset is LitExpr<*> }
  val refs = labels.sumOf { it.references.size }

  fun kind(l: XcfaLabel): String =
    when (l) {
      is InvokeLabel -> if (l.isLibraryFunction) "library-call" else "call"
      is StartLabel -> "thread-start"
      is JoinLabel -> "thread-join"
      is AtomicBeginLabel,
      is AtomicEndLabel -> "atomic"
      is MutexLockLabel,
      is MutexUnlockLabel,
      is MutexTryLockLabel -> "mutex"
      is NondetLabel -> "nondet-branch"
      is StmtLabel ->
        when (l.stmt) {
          is AssignStmt<*> -> "assign"
          is AssumeStmt -> "assume"
          is HavocStmt<*> -> "havoc"
          is MemoryAssignStmt<*, *, *> -> "memory-assign"
          else -> "other-stmt"
        }
      is NopLabel -> "nop"
      else -> "other"
    }
  val labelKinds = labels.groupingBy { kind(it) }.eachCount()

  fun j(vararg pairs: Pair<String, Any?>): String =
    pairs.joinToString(",", "{", "}") { (k, v) ->
      val rendered =
        when (v) {
          is Number,
          is Boolean -> v.toString()
          is Map<*, *> -> v.entries.joinToString(",", "{", "}") { "\"${it.key}\":${it.value}" }
          is Collection<*> ->
            v.joinToString(",", "[", "]") { e -> if (e is Number) e.toString() else "\"$e\"" }
          else -> "\"$v\""
        }
      "\"$k\":$rendered"
    }

  return j(
    "property" to property,
    "propertyFile" to propertyFile,
    // encoding and theories
    "arithmetic" to parseContext.arithmetic.name,
    "arithmeticAutoSelected" to parseContext.isArithmeticAutoSelected,
    "arithmeticTraits" to parseContext.arithmeticTraits.map { it.name }.sorted(),
    "multiThreading" to parseContext.multiThreading,
    "smtTypes" to typeNames.groupingBy { it }.eachCount(),
    "bvWidths" to bvWidths,
    // size
    "procedures" to procs.size,
    "locations" to locs.size,
    "edges" to edges.size,
    "maxLocationsPerProc" to (procs.maxOfOrNull { it.locs.size } ?: 0),
    "maxEdgesPerProc" to (procs.maxOfOrNull { it.edges.size } ?: 0),
    "globalVars" to xcfa.globalVars.size,
    "localVars" to procs.sumOf { it.vars.size },
    "params" to procs.sumOf { it.params.size },
    "labels" to labels.size,
    // control flow
    "cyclomatic" to cyclomatic,
    "maxCyclomatic" to maxCyclomatic,
    "backEdges" to backEdges,
    "cyclicProcedures" to cyclicProcs,
    "acyclic" to (backEdges == 0),
    "branchingLocations" to branching,
    "inlined" to xcfa.isInlined,
    "unsafeUnrollUsed" to xcfa.unsafeUnrollUsed,
    "errorLocations" to procs.count { it.errorLoc.isPresent },
    "initProcedures" to xcfa.initProcedures.size,
    // memory
    "dereferences" to derefs.size,
    "dereferenceReads" to derefReads,
    "dereferenceWrites" to derefWrites,
    "constantOffsetDereferences" to constOffsets,
    "references" to refs,
    "aliasGraphSize" to xcfa.pointsToGraph.size,
    "aliasGraphMaxFanout" to (xcfa.pointsToGraph.values.maxOfOrNull { it.size } ?: 0),
    // statement mix
    "labelKinds" to labelKinds,
    "havocs" to (labelKinds["havoc"] ?: 0),
    // what the program's own C code is made of, counted over the declarations it actually uses
    "source" to parseContext.sourceTraits,
    "assumes" to (labelKinds["assume"] ?: 0),
    "calls" to (labelKinds["call"] ?: 0),
    "libraryCalls" to (labelKinds["library-call"] ?: 0),
  )
}

private fun Type.smtName(): String =
  when (this) {
    is IntType -> "Int"
    is BoolType -> "Bool"
    is RatType -> "Rat"
    is FpType -> "Fp${exponent}_${significand}"
    is BvType -> "Bv$size"
    is ArrayType<*, *> -> "Array"
    else -> javaClass.simpleName
  }

/** Back edges, found with an iterative DFS so deep inlining cannot overflow the stack. */
private fun XcfaProcedure.backEdgeCount(): Int {
  val succ = edges.groupBy({ it.source }, { it.target })
  val visited = mutableSetOf<XcfaLocation>()
  val onStack = mutableSetOf<XcfaLocation>()
  var back = 0
  for (start in locs) {
    if (start in visited) continue
    val stack = ArrayDeque<Pair<XcfaLocation, Iterator<XcfaLocation>>>()
    visited.add(start)
    onStack.add(start)
    stack.addLast(start to succ[start].orEmpty().iterator())
    while (stack.isNotEmpty()) {
      val (loc, iter) = stack.last()
      if (iter.hasNext()) {
        val next = iter.next()
        if (next in onStack) back++
        else if (next !in visited) {
          visited.add(next)
          onStack.add(next)
          stack.addLast(next to succ[next].orEmpty().iterator())
        }
      } else {
        onStack.remove(loc)
        stack.removeLast()
      }
    }
  }
  return back
}
