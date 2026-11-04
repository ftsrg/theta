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
package hu.bme.mit.theta.xcfa2chc

import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Skip
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.model.AtomicBeginLabel
import hu.bme.mit.theta.xcfa.model.AtomicEndLabel
import hu.bme.mit.theta.xcfa.model.JoinLabel
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Thread-modular (Owicki-Gries style) CHC encoding for any number of threads: every location gets a
 * relation over the shared globals and the procedure's locals, closed (outside atomic blocks) under
 * an `Env(G, G')` relation of every global change by any thread. A thread start implies the started
 * procedure's initial location with its parameters bound to the arguments; joins are no-ops.
 *
 * This over-approximates every interleaving, so only a satisfiable (safe) system is conclusive; an
 * unsatisfiable one may be spurious. Labels it could not over-approximate (mutexes, which have to
 * be eliminated first, calls) are rejected.
 */
fun XCFA.toThreadModularCHC(): List<Relation> {
  val initProcedure = initProcedures.singleOrNull()?.first ?: error("Exactly one entry is needed")

  val threadLocalGlobals = globalVars.filter { it.threadLocal }.map { it.wrappedVar }.toSet()
  val sharedGlobalCandidates = globalVars.filter { !it.threadLocal }.map { it.wrappedVar }.toSet()

  val procedureVars =
    procedures.associateWith { proc ->
      (proc.edges.flatMap { it.label.collectVars() } + proc.params.map { it.first }).toSet()
    }
  val shared = procedureVars.values.flatten().filter { it in sharedGlobalCandidates }.distinct()
  val locals =
    procedureVars.mapValues { (_, vars) ->
      vars.filter { it !in sharedGlobalCandidates || it in threadLocalGlobals }.distinct()
    }

  // Unique parameter names, as the locals of different procedures may share names.
  var paramCnt = 0
  fun params(vars: List<VarDecl<*>>, suffix: String): Map<VarDecl<*>, ParamDecl<*>> =
    vars.associateWith { Param("|${it.name}_${suffix}${paramCnt++}|", it.type) }

  val sharedOld = params(shared, "")
  val sharedNew = params(shared, "new")
  val localOld = locals.mapValues { (_, vars) -> params(vars, "") }
  val localNew = locals.mapValues { (_, vars) -> params(vars, "new") }
  // Locals of a started thread, kept apart from the starter's (a procedure may start itself).
  val localStarted = locals.mapValues { (_, vars) -> params(vars, "start") }

  // A relation over no variables is not supported, so such procedures get a dummy argument.
  val dummy = Param("__tm_dummy", Int())
  fun args(
    proc: XcfaProcedure,
    g: Map<VarDecl<*>, ParamDecl<*>>,
    l: Map<VarDecl<*>, ParamDecl<*>>,
  ) =
    (shared.map { g[it]!!.ref } + locals[proc]!!.map { l[it]!!.ref }).ifEmpty { listOf(dummy.ref) }

  val relations = mutableListOf<Relation>()
  val locRelations =
    procedures
      .mapIndexed { i, proc ->
        val types =
          (shared + locals[proc]!!).map { it.type }.ifEmpty { listOf(Int()) }.toTypedArray()
        proc to
          proc.locs.associateWith { loc ->
            Relation("P${i}_${loc.name}", *types).also { relations.add(it) }
          }
      }
      .toMap()
  val env =
    if (shared.isEmpty()) null
    else Relation("Env", *(shared + shared).map { it.type }.toTypedArray()).also(relations::add)
  val envApp = { from: Map<VarDecl<*>, ParamDecl<*>>, to: Map<VarDecl<*>, ParamDecl<*>> ->
    env!!(shared.map { from[it]!!.ref } + shared.map { to[it]!!.ref })
  }

  locRelations[initProcedure]!![initProcedure.initLoc]!!(
    args(initProcedure, sharedOld, localOld[initProcedure]!!)
  ) += True()

  for (proc in procedures) {
    val rels = locRelations[proc]!!
    val vars = shared + locals[proc]!!
    val oldParams = sharedOld + localOld[proc]!!
    val newParams = sharedNew + localNew[proc]!!

    for (edge in proc.edges) {
      val flat = edge.label.getFlatLabels()
      val stmts = flat.map { it.toThreadModularStmt() }
      val unfoldResult =
        StmtUtils.toExpr(SequenceStmt.of(stmts), VarIndexingFactory.basicVarIndexing(0))
      val transExpr = PathUtils.unfold(And(unfoldResult.exprs), VarIndexingFactory.indexing(0))

      // Arguments of thread starts, evaluated at their position within the edge.
      val starts =
        flat.mapIndexedNotNull { i, label ->
          (label as? StartLabel)?.let {
            val indexing =
              StmtUtils.toExpr(
                  SequenceStmt.of(stmts.subList(0, i)),
                  VarIndexingFactory.basicVarIndexing(0),
                )
                .indexing
            it to startArgs(it, indexing)
          }
        }

      val finalIndexing = unfoldResult.indexing
      var cnt = 0
      val allExprs = listOf(transExpr) + starts.flatMap { it.second.values }
      val consts =
        allExprs
          .flatMap { ExprUtils.getIndexedConstants(it) }
          .toSet()
          .associateWith {
            if (it.index == 0) oldParams[it.varDecl]!!
            else if (it.index == finalIndexing[it.varDecl]) newParams[it.varDecl]!!
            else Param("__tm_tmp_${cnt++}", it.type)
          }
      val trans = ExprUtils.changeDecls(transExpr, consts)
      val postParams =
        vars.associateWith { if (finalIndexing[it] == 0) oldParams[it]!! else newParams[it]!! }
      val postShared = shared.associateWith { postParams[it]!! }
      val source = rels[edge.source]!!(args(proc, sharedOld, localOld[proc]!!))

      rels[edge.target]!!(args(proc, postShared, postParams)) += listOf(source.expr, trans)

      if (env != null && shared.any { finalIndexing[it] != 0 }) {
        envApp(sharedOld, postShared) += listOf(source.expr, trans)
      }

      for ((start, startArgs) in starts) {
        val started =
          procedures.find { it.name == start.name } ?: error("No procedure ${start.name} to start")
        val startedLocals = localStarted[started]!!
        val bindings =
          startArgs.map { (param, arg) ->
            Eq(startedLocals[param]!!.ref, ExprUtils.changeDecls(arg, consts))
          }
        locRelations[started]!![started.initLoc]!!(args(started, postShared, startedLocals)) +=
          listOf(source.expr, trans) + bindings
      }
    }

    if (env != null) {
      val atomicLocs = proc.atomicLocations()
      for ((loc, rel) in rels) {
        if (loc in atomicLocs) continue
        rel(args(proc, sharedNew, localOld[proc]!!)) +=
          listOf(
            rel(args(proc, sharedOld, localOld[proc]!!)).expr,
            envApp(sharedOld, sharedNew).expr,
          )
      }
    }

    proc.errorLoc.ifPresent { !(rels[it]!!(args(proc, sharedOld, localOld[proc]!!))) }
  }

  return relations
}

/** The started procedure's input parameters bound to the start's arguments, unfolded. */
private fun XCFA.startArgs(start: StartLabel, indexing: VarIndexing): Map<VarDecl<*>, Expr<*>> {
  val started = procedures.find { it.name == start.name } ?: error("No procedure ${start.name}")
  // params[0] of a start is the return value, as with invocations.
  return started.params
    .filter { it.second != ParamDirection.OUT }
    .mapIndexed { i, (param, _) -> param to PathUtils.unfold(start.params[i + 1], indexing) }
    .toMap()
}

private fun XcfaLabel.toThreadModularStmt(): Stmt =
  when (this) {
    is StmtLabel -> stmt
    is NopLabel,
    is AtomicBeginLabel,
    is AtomicEndLabel,
    // A join waits for the thread to end; not waiting only adds behaviors.
    is JoinLabel -> Skip()
    // The thread id is not tracked: any value over-approximates.
    is StartLabel -> HavocStmt.of(pidVar)
    is NondetLabel -> {
      check(isPlainStmt()) { "Thread-modular CHC encoding does not support $this" }
      toStmt()
    }
    else -> error("Thread-modular CHC encoding does not support label $this")
  }

private fun XcfaLabel.isPlainStmt(): Boolean =
  when (this) {
    is StmtLabel,
    is NopLabel -> true
    is SequenceLabel -> labels.all { it.isPlainStmt() }
    is NondetLabel -> labels.all { it.isPlainStmt() }
    else -> false
  }

/**
 * Locations inside an atomic block, where no other thread can interfere. A location reachable both
 * inside and outside an atomic block cannot be classified, so it is rejected.
 */
private fun XcfaProcedure.atomicLocations(): Set<XcfaLocation> {
  val depth = mutableMapOf(initLoc to 0)
  val waitlist = ArrayDeque(listOf(initLoc))
  while (waitlist.isNotEmpty()) {
    val loc = waitlist.removeFirst()
    for (edge: XcfaEdge in loc.outgoingEdges) {
      var d = depth[loc]!!
      for (label in edge.label.getFlatLabels()) {
        when (label) {
          is AtomicBeginLabel -> d++
          is AtomicEndLabel -> d--
          is NondetLabel ->
            check(
              label.labels.none { l ->
                l.getFlatLabels().any { it is AtomicBeginLabel || it is AtomicEndLabel }
              }
            ) {
              "Atomic fence in a nondeterministic choice: $label"
            }
          else -> {}
        }
        check(d >= 0) { "Unbalanced atomic block at ${edge.source} -> ${edge.target}" }
      }
      val known = depth[edge.target]
      if (known == null) {
        depth[edge.target] = d
        waitlist.add(edge.target)
      } else {
        check(known == d) {
          "Location ${edge.target} is reachable both in and out of an atomic block"
        }
      }
    }
  }
  return depth.filterValues { it > 0 }.keys
}
