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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.rattype.RatEqExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
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
 * Existential variables for havocs in violation conditions, interned by `(index, type)` and
 * renumbered by [canonicalize] so that equal conditions are structurally equal.
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

  fun indexOf(decl: VarDecl<*>): Int? = keyOf[decl]?.index

  fun of(index: Int, type: Type): VarDecl<*> = get(index, type)

  fun collectVars(expr: Expr<*>): List<VarDecl<*>> =
    linkedSetOf<VarDecl<*>>().also { ExprUtils.collectVars(expr, it) }.filter(::isAux)

  fun <T : Type> canonicalize(expr: Expr<T>): Expr<T> {
    val vars = collectVars(expr)
    if (vars.isEmpty()) return expr
    val substitution = BasicSubstitution.builder()
    vars.forEachIndexed { index, decl -> substitution.put(decl, get(index, decl.type).ref) }
    return substitution.build().apply(expr)
  }

  /** The first index no auxiliary variable of [expr] uses. */
  fun nextIndex(expr: Expr<*>): Int =
    collectVars(expr).mapNotNull(::indexOf).maxOrNull()?.plus(1) ?: 0

  /** [expr] with its auxiliary variables moved by [offset], so a conjunction keeps them apart. */
  fun <T : Type> shift(expr: Expr<T>, offset: Int): Expr<T> {
    val vars = collectVars(expr)
    if (vars.isEmpty() || offset == 0) return expr
    val substitution = BasicSubstitution.builder()
    for (decl in vars) substitution.put(decl, get(indexOf(decl)!! + offset, decl.type).ref)
    return substitution.build().apply(expr)
  }
}

/** CPAchecker's `ViolationConditionOperator`: the weakest precondition of reaching [targets]. */
fun computeViolationCondition(
  block: Block,
  targets: Map<XcfaLocation, Expr<BoolType>>,
): Expr<BoolType> =
  BackwardConditions(block, targets).let { conditions ->
    toViolationCondition(
      orStates(conditions.entryEdges.map { wep(it.label, conditions.at(it.target)) })
    )
  }

private class BackwardConditions(
  private val block: Block,
  private val targets: Map<XcfaLocation, Expr<BoolType>>,
) {

  private val memo = HashMap<XcfaLocation, WpState>()
  private val onStack = HashSet<XcfaLocation>()

  val entryEdges: List<XcfaEdge> = block.initialLocation.outgoingEdges.filter { it in block.edges }

  fun edgesFrom(location: XcfaLocation): List<XcfaEdge> =
    location.outgoingEdges.filter { it in block.edges && location != block.finalLocation }

  fun at(location: XcfaLocation): WpState {
    memo[location]?.let {
      return it
    }
    check(onStack.add(location)) {
      "Block ${block.id} contains a cycle through ${location.name}; violation conditions can only " +
        "be computed for acyclic blocks"
    }
    val disjuncts = mutableListOf<WpState>()
    targets[location]?.let { disjuncts += WpState.of(it) }
    for (edge in edgesFrom(location)) disjuncts += wep(edge.label, at(edge.target))
    onStack.remove(location)
    return orStates(disjuncts).also { memo[location] = it }
  }
}

/**
 * [computeViolationCondition] over the paths of [block] that take at most [unrollings] back edges
 * of a depth-first search from its entry, so for blocks with internal cycles too. It
 * under-approximates the weakest precondition: a start state outside it reaches [targets] along no
 * such path, maybe along a longer one.
 */
fun computeBoundedViolationCondition(
  block: Block,
  targets: Map<XcfaLocation, Expr<BoolType>>,
  unrollings: Int,
): Expr<BoolType> {
  require(unrollings >= 0) { "Negative unrolling bound: $unrollings" }
  val conditions = BoundedBackwardConditions(block, targets, unrollings)
  return toViolationCondition(
    orStates(conditions.entryEdges.mapNotNull { conditions.through(it, taken = 0) })
  )
}

private class BoundedBackwardConditions(
  private val block: Block,
  private val targets: Map<XcfaLocation, Expr<BoolType>>,
  private val unrollings: Int,
) {

  val entryEdges: List<XcfaEdge> = block.initialLocation.outgoingEdges.filter { it in block.edges }

  private fun edgesFrom(location: XcfaLocation): List<XcfaEdge> =
    location.outgoingEdges.filter { it in block.edges && location != block.finalLocation }

  /** Without these the block is acyclic, and each one taken moves a path to the next copy. */
  private val backEdges: Set<XcfaEdge> =
    HashSet<XcfaEdge>().also { back ->
      val done = HashSet<XcfaLocation>()
      val onStack = HashSet<XcfaLocation>()
      fun visit(location: XcfaLocation) {
        onStack += location
        for (edge in edgesFrom(location)) {
          if (edge.target in onStack) back += edge else if (edge.target !in done) visit(edge.target)
        }
        onStack -= location
        done += location
      }
      // A split loop head ends the block where it starts: an edge into it closes no cycle
      if (block.initialLocation != block.finalLocation) visit(block.initialLocation)
      else entryEdges.forEach { if (it.target !in done) visit(it.target) }
    }

  private val memo = HashMap<Pair<XcfaLocation, Int>, WpState>()

  /** The condition of taking [edge] after [taken] back edges, or null past the bound. */
  fun through(edge: XcfaEdge, taken: Int): WpState? {
    val next = if (edge in backEdges) taken + 1 else taken
    return if (next > unrollings) null else wep(edge.label, at(edge.target, next))
  }

  private fun at(location: XcfaLocation, taken: Int): WpState {
    memo[location to taken]?.let {
      return it
    }
    val disjuncts = mutableListOf<WpState>()
    targets[location]?.let { disjuncts += WpState.of(it) }
    for (edge in edgesFrom(location)) through(edge, taken)?.let { disjuncts += it }
    return orStates(disjuncts).also { memo[location to taken] = it }
  }
}

class BlockRun(val edges: List<XcfaEdge>, val end: XcfaLocation, val state: Valuation)

/** A concrete run of acyclic [block] from [entry] to one of [targets], for violation witnesses. */
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
        followPath(solver, state, listOf(edge), conditions.at(edge.target).expr)?.let { edge to it }
      } ?: return null
    edges += edge
    state = next
    location = edge.target
    candidates = conditions.edgesFrom(location)
  }
}

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

/** A cycle other than a split loop head; [computeViolationCondition] can't handle these. */
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
          (!splitHead || location != block.finalLocation) &&
          cycleFrom(edge.target)
      }
    onStack.remove(location)
    done.add(location)
    return cyclic
  }

  return block.initialLocation.outgoingEdges.any { it in block.edges && cycleFrom(it.target) }
}

/** The violation condition of a single path, for blocks with an internal cycle. */
fun computePathViolationCondition(labels: List<XcfaLabel>): Expr<BoolType> =
  toViolationCondition(labels.foldRight(WpState.of(True())) { label, post -> wep(label, post) })

private fun wep(label: XcfaLabel, post: WpState): WpState {
  checkSupported(label)
  return if (post.expr == False()) post else post.wep(label.toStmt())
}

/**
 * `toStmt` turns labels it cannot express (calls, fences, ...) into skips, which is unsound here.
 */
private fun checkSupported(label: XcfaLabel) {
  when (label) {
    is NopLabel,
    is StmtLabel -> {}
    is SequenceLabel -> label.labels.forEach(::checkSupported)
    is NondetLabel -> label.labels.forEach(::checkSupported)
    else ->
      throw UnsupportedOperationException(
        "DSS cannot compute violation conditions over $label (${label.javaClass.simpleName})"
      )
  }
}

/** Havocs become [DssAuxVars]: unlike [WpState]'s constants, predecessors can havoc them. */
private fun toViolationCondition(state: WpState): Expr<BoolType> {
  val expr = ExprUtils.simplify(state.expr)
  val havocs = ExprUtils.getConstants(expr).filter { it.name.startsWith(WP_CONST_PREFIX) }
  if (havocs.isEmpty()) return DssAuxVars.canonicalize(expr)
  val next = DssAuxVars.collectVars(expr).mapNotNull(DssAuxVars::indexOf).maxOrNull()?.plus(1) ?: 0
  val substitution = BasicSubstitution.builder()
  havocs.forEachIndexed { i, const ->
    substitution.put(const, DssAuxVars.of(next + i, const.type).ref)
  }
  return DssAuxVars.canonicalize(substitution.build().apply(expr))
}

private const val WP_CONST_PREFIX = "_wp_"

private fun orStates(disjuncts: List<WpState>): WpState =
  WpState.of(or(disjuncts.map { it.expr }), disjuncts.maxOfOrNull { it.constCount } ?: 0)

/** Factors `(c1 && φ) || (c2 && φ)` into `(c1 || c2) && φ`, or conditions double per branch. */
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

/**
 * A condition without auxiliary variables equivalent to [condition], or null if there is none this
 * way. An auxiliary variable a conjunct defines as `a == t` is first replaced by `t` (see
 * [substituteAuxDefinitions]). Conjuncts linked by shared auxiliary variables but no program
 * variable constrain only the havocked values: they are dropped if satisfiable ([isSatisfiable]),
 * else the condition is false.
 */
fun withoutAuxVars(
  condition: Expr<BoolType>,
  isSatisfiable: (Expr<BoolType>) -> Boolean,
): Expr<BoolType>? {
  fun conjuncts(expr: Expr<BoolType>): List<Expr<BoolType>> =
    if (expr is AndExpr) expr.ops.flatMap(::conjuncts) else listOf(expr)
  val components = mutableListOf<Pair<MutableSet<VarDecl<*>>, MutableList<Expr<BoolType>>>>()
  for (conjunct in substituteAuxDefinitions(conjuncts(condition))) {
    val vars = ExprUtils.getVars(conjunct).toMutableSet()
    val linked =
      components.filter { (other, _) -> vars.any { it in other && DssAuxVars.isAux(it) } }
    components.removeAll(linked)
    val exprs = linked.flatMap { it.second }.toMutableList().apply { add(conjunct) }
    linked.forEach { vars.addAll(it.first) }
    components += vars to exprs
  }
  val kept = mutableListOf<Expr<BoolType>>()
  for ((vars, exprs) in components) {
    when {
      vars.none(DssAuxVars::isAux) -> kept += exprs
      vars.any { !DssAuxVars.isAux(it) } -> return null
      !isSatisfiable(And(exprs)) -> return False()
    }
  }
  return And(kept)
}

/**
 * [conjuncts] without the definitions `a == t` of auxiliary variables `a` not in `t`, with `t` put
 * for `a`: `exists a. a == t && P(a)` is `P(t)`. A reversed `x := f(x)` havocs the old value of `x`
 * and then defines it so. Only exact equalities count: an IEEE `fp.eq` is none.
 */
private fun substituteAuxDefinitions(conjuncts: List<Expr<BoolType>>): List<Expr<BoolType>> {
  var current = conjuncts
  while (true) {
    val (definition, aux, value) =
      current.firstNotNullOfOrNull { conjunct ->
        auxDefinition(conjunct)?.let { (aux, value) -> Triple(conjunct, aux, value) }
      } ?: return current
    val substitution = BasicSubstitution.builder().put(aux, value).build()
    current = current.filter { it !== definition }.map { substitution.apply(it) }
  }
}

private fun auxDefinition(conjunct: Expr<BoolType>): Pair<VarDecl<*>, Expr<*>>? {
  val equality =
    when (conjunct) {
      is IntEqExpr,
      is RatEqExpr,
      is BvEqExpr,
      is IffExpr,
      is ArrayEqExpr<*, *> -> conjunct as EqExpr<*>
      else -> return null
    }
  for ((side, other) in
    listOf(equality.leftOp to equality.rightOp, equality.rightOp to equality.leftOp)) {
    val decl = (side as? RefExpr<*>)?.decl as? VarDecl<*> ?: continue
    if (DssAuxVars.isAux(decl) && decl !in ExprUtils.getVars(other)) return decl to other
  }
  return null
}
