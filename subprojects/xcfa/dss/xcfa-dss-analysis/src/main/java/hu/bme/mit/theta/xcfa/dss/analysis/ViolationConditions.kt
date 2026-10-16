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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.GhostEdgeMetadata
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

/**
 * Existentially quantified auxiliary variables encoding havocs in violation conditions (CPAchecker
 * uses SSA variables), interned by `(index, type)` and renumbered by [canonicalize] for equality.
 */
object DssAuxVars {

  private const val PREFIX = "__dss_vc_"

  private data class Key(val index: Int, val type: Type)

  private val byKey = ConcurrentHashMap<Key, VarDecl<*>>()
  private val keyOf = ConcurrentHashMap<VarDecl<*>, Key>()
  private val names = AtomicInteger()

  private fun get(index: Int, type: Type): VarDecl<*> =
    byKey.computeIfAbsent(Key(index, type)) { key ->
      Var("$PREFIX${names.getAndIncrement()}", type).also { keyOf[it] = key }
    }

  fun isAux(decl: VarDecl<*>): Boolean = keyOf.containsKey(decl)

  /**
   * The interning index of an auxiliary variable, or null for any other variable. Together with the
   * type it identifies the variable across processes, where the names differ.
   */
  fun indexOf(decl: VarDecl<*>): Int? = keyOf[decl]?.index

  /** The auxiliary variable of [index] and [type] in this process. */
  fun of(index: Int, type: Type): VarDecl<*> = get(index, type)

  /** The auxiliary variables of [expr], in order of first occurrence. */
  fun collectVars(expr: Expr<*>): List<VarDecl<*>> =
    linkedSetOf<VarDecl<*>>().also { ExprUtils.collectVars(expr, it) }.filter(::isAux)

  /** An auxiliary variable of [type] that does not occur in [expr]. */
  fun freshFor(expr: Expr<*>, type: Type): VarDecl<*> {
    val next = collectVars(expr).maxOfOrNull { keyOf.getValue(it).index }?.plus(1) ?: 0
    return get(next, type)
  }

  /** Renumbers the auxiliary variables of [expr] by first occurrence. */
  fun <T : Type> canonicalize(expr: Expr<T>): Expr<T> {
    val vars = collectVars(expr)
    if (vars.isEmpty()) return expr
    val substitution = BasicSubstitution.builder()
    vars.forEachIndexed { index, decl -> substitution.put(decl, get(index, decl.type).ref) }
    return substitution.build().apply(expr)
  }
}

/**
 * `packVcond` (CPAchecker's `ViolationConditionOperator`): the weakest existential precondition at
 * the block entry of reaching one of [targets], over all block paths; unsupported labels throw.
 */
fun computeViolationCondition(
  block: Block,
  targets: Map<XcfaLocation, Expr<BoolType>>,
): Expr<BoolType> =
  BackwardConditions(block, targets).let { conditions ->
    val fromEntry = or(conditions.entryEdges.map { wep(it.label, conditions.at(it.target)) })
    DssAuxVars.canonicalize(ExprUtils.simplify(fromEntry))
  }

/** The weakest existential precondition of reaching one of [targets] from each block location. */
private class BackwardConditions(
  private val block: Block,
  private val targets: Map<XcfaLocation, Expr<BoolType>>,
) {

  private val memo = HashMap<XcfaLocation, Expr<BoolType>>()
  private val onStack = HashSet<XcfaLocation>()

  /** The block's edges leaving its entry, i.e., before the first edge is processed. */
  val entryEdges: List<XcfaEdge> =
    block.initialLocation.outgoingEdges.filter {
      it in block.edges && it.metadata != GhostEdgeMetadata
    }

  /** The block ends at its final location; only the ghost edge may be followed from there. */
  fun edgesFrom(location: XcfaLocation): List<XcfaEdge> =
    location.outgoingEdges.filter {
      it in block.edges && (location != block.finalLocation || it.metadata == GhostEdgeMetadata)
    }

  fun at(location: XcfaLocation): Expr<BoolType> {
    memo[location]?.let {
      return it
    }
    check(onStack.add(location)) {
      "Block ${block.id} contains a cycle through ${location.name}; violation conditions can only " +
        "be computed for acyclic blocks"
    }
    val disjuncts = mutableListOf<Expr<BoolType>>()
    targets[location]?.let(disjuncts::add)
    for (edge in edgesFrom(location)) disjuncts += wep(edge.label, at(edge.target))
    onStack.remove(location)
    return or(disjuncts).also { memo[location] = it }
  }
}

/**
 * A concrete run of a block: its [edges] from the entry to the target [end], and the [state] there.
 */
class BlockRun(val edges: List<XcfaEdge>, val end: XcfaLocation, val state: Valuation)

/**
 * A run of acyclic [block] from the concrete [entry] state to one of [targets]: at every location
 * it takes an edge from which a target stays reachable ([computeViolationCondition]'s conditions).
 */
fun findBlockRun(
  block: Block,
  targets: Map<XcfaLocation, Expr<BoolType>>,
  entry: Valuation,
  solver: Solver,
): BlockRun? {
  val conditions = BackwardConditions(block, targets)
  val edges = mutableListOf<XcfaEdge>()
  var location = block.initialLocation
  var state = entry
  var candidates = conditions.entryEdges
  while (true) {
    val target = targets[location]
    if (
      edges.isNotEmpty() && target != null && followPath(solver, state, emptyList(), target) != null
    ) {
      return BlockRun(edges, location, state)
    }
    val (edge, next) =
      candidates.firstNotNullOfOrNull { edge ->
        followPath(solver, state, listOf(edge), conditions.at(edge.target))?.let { edge to it }
      } ?: return null
    edges += edge
    state = next
    location = edge.target
    candidates = conditions.edgesFrom(location)
  }
}

/**
 * The state reached from the concrete [state] along [edges] in a run that ends in [target], or null
 * if there is none. Auxiliary variables ([DssAuxVars]) are existential, so they are left out.
 */
fun followPath(
  solver: Solver,
  state: Valuation,
  edges: List<XcfaEdge>,
  target: Expr<BoolType>,
): Valuation? {
  var indexing = VarIndexingFactory.indexing(0)
  WithPushPop(solver).use {
    solver.add(PathUtils.unfold(state.toExpr(), indexing))
    for (edge in edges) {
      val action = XcfaAction(0, edge)
      solver.add(PathUtils.unfold(action.toExpr(), indexing))
      indexing = indexing.add(action.nextIndexing())
    }
    solver.add(PathUtils.unfold(target, indexing))
    if (!solver.check().isSat) return null
    val reached = PathUtils.extractValuation(solver.model, indexing).toMap()
    return ImmutableValuation.from(reached.filterKeys { it is VarDecl<*> && !DssAuxVars.isAux(it) })
  }
}

/**
 * Whether [block] has a cycle other than a loop body from and to the loop head, which
 * [computeViolationCondition] can't handle (only `SelfLoopAbsorbingDecomposition` makes these).
 */
fun hasInternalCycle(block: Block): Boolean {
  val done = HashSet<XcfaLocation>()
  val onStack = HashSet<XcfaLocation>()
  val splitHead = block.initialLocation == block.finalLocation

  fun cycleFrom(location: XcfaLocation): Boolean {
    if (location in done) return false
    if (!onStack.add(location)) return true
    val cyclic =
      location.outgoingEdges.any { edge ->
        edge in block.edges &&
          (!splitHead || location != block.finalLocation || edge.metadata == GhostEdgeMetadata) &&
          cycleFrom(edge.target)
      }
    onStack.remove(location)
    done.add(location)
    return cyclic
  }

  return block.initialLocation.outgoingEdges.any {
    it in block.edges && it.metadata != GhostEdgeMetadata && cycleFrom(it.target)
  }
}

/**
 * The violation condition of a single path [labels] to a target, for blocks with an internal cycle
 * ([hasInternalCycle]): each refuted counterexample pushes the next one onto another path.
 */
fun computePathViolationCondition(labels: List<XcfaLabel>): Expr<BoolType> =
  DssAuxVars.canonicalize(
    ExprUtils.simplify(
      labels.foldRight<XcfaLabel, Expr<BoolType>>(True()) { label, post -> wep(label, post) }
    )
  )

private fun wep(label: XcfaLabel, post: Expr<BoolType>): Expr<BoolType> =
  if (post == False()) False()
  else
    when (label) {
      is NopLabel -> post
      is StmtLabel -> wep(label.stmt, post)
      is SequenceLabel -> label.labels.foldRight(post) { l, acc -> wep(l, acc) }
      is NondetLabel -> or(label.labels.map { wep(it, post) })
      else ->
        throw UnsupportedOperationException(
          "DSS cannot compute violation conditions over $label (${label.javaClass.simpleName})"
        )
    }

private fun wep(stmt: Stmt, post: Expr<BoolType>): Expr<BoolType> =
  if (post == False()) False()
  else
    when (stmt) {
      is SkipStmt,
      is AssumeStmt,
      is AssignStmt<*> -> WpState.of(post).wep(stmt).expr
      // WpState havocs to a fresh constant; DSS needs an auxiliary variable instead, which the
      // predecessor block can havoc and other processes can intern (see DssAuxVars).
      is HavocStmt<*> ->
        BasicSubstitution.builder()
          .put(stmt.varDecl, DssAuxVars.freshFor(post, stmt.varDecl.type).ref)
          .build()
          .apply(post)
      is SequenceStmt -> stmt.stmts.foldRight(post) { s, acc -> wep(s, acc) }
      is NonDetStmt -> or(stmt.stmts.map { wep(it, post) })
      else ->
        throw UnsupportedOperationException(
          "DSS cannot compute violation conditions over $stmt (${stmt.javaClass.simpleName})"
        )
    }

/**
 * [Or] that factors `(c1 && φ) || (c2 && φ)` into `(c1 || c2) && φ`, so conditions don't double at
 * every branch point.
 */
private fun or(disjuncts: List<Expr<BoolType>>): Expr<BoolType> {
  val relevant = disjuncts.filter { it != False() }.distinct()
  if (relevant.size <= 1 || True() in relevant) return Or(relevant)
  val byContinuation = LinkedHashMap<Expr<BoolType>?, MutableList<Expr<BoolType>>>()
  for (disjunct in relevant) {
    if (disjunct is AndExpr && disjunct.ops.size == 2) {
      byContinuation.getOrPut(disjunct.ops[1]) { mutableListOf() } += disjunct.ops[0]
    } else {
      byContinuation.getOrPut(null) { mutableListOf() } += disjunct
    }
  }
  val factored =
    byContinuation.flatMap { (continuation, heads) ->
      when {
        continuation == null -> heads
        heads.size == 1 -> listOf(And(heads.single(), continuation))
        else -> listOf(And(or(heads), continuation))
      }
    }
  return Or(factored)
}
