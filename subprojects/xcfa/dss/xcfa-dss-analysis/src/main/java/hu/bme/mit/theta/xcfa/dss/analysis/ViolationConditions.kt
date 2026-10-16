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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.GhostEdgeMetadata
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.IdentityHashMap
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

/**
 * Existentially quantified auxiliary variables of violation conditions.
 *
 * CPAchecker represents a violation condition as a path formula in SSA form: a value that a
 * `__VERIFIER_nondet_*()` call (a havoc) produced along the path is just another SSA variable of
 * the formula, implicitly existentially quantified. Theta's violation conditions are plain
 * expressions over the procedure's variables (so that they can be put on an `assume` edge of the
 * predecessor block), so a havoc is encoded by substituting a fresh auxiliary variable instead; the
 * predecessor block havocs every auxiliary variable right before assuming the condition (see
 * [extractBlockXcfa]), which is exactly the existential quantification.
 *
 * Auxiliary variables are interned by `(index, type)` and every violation condition is renumbered
 * canonically by [canonicalize] (first occurrence gets index 0, and so on). This keeps
 * syntactically identical conditions structurally equal, which DSS relies on to recognize repeated
 * violation conditions (CPAchecker compares the `ViolationWitness`es, i.e., the edges of the paths,
 * for the same purpose).
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
  fun varsOf(expr: Expr<*>): List<VarDecl<*>> {
    val result = linkedSetOf<VarDecl<*>>()
    val visited = IdentityHashMap<Expr<*>, Unit>()
    fun visit(e: Expr<*>) {
      if (visited.put(e, Unit) != null) return
      if (e is RefExpr<*>) {
        val decl = e.decl
        if (decl is VarDecl<*> && isAux(decl)) result += decl
      }
      e.ops.forEach(::visit)
    }
    visit(expr)
    return result.toList()
  }

  /** An auxiliary variable of [type] that does not occur in [expr]. */
  fun freshFor(expr: Expr<*>, type: Type): VarDecl<*> {
    val next = varsOf(expr).maxOfOrNull { keyOf.getValue(it).index }?.plus(1) ?: 0
    return get(next, type)
  }

  /** Renumbers the auxiliary variables of [expr] by first occurrence. */
  fun <T : Type> canonicalize(expr: Expr<T>): Expr<T> {
    val vars = varsOf(expr)
    if (vars.isEmpty()) return expr
    val substitution = BasicSubstitution.builder()
    vars.forEachIndexed { index, decl -> substitution.put(decl, get(index, decl.type).ref) }
    return substitution.build().apply(expr)
  }
}

/**
 * Computes the violation condition of [block] (CPAchecker's `ViolationConditionOperator`, paper:
 * `packVcond`): the weakest existential precondition, at the block entry, of reaching one of
 * [targets] - a location mapped to the condition that has to hold there (`True()` for the block's
 * own error locations, the received violation conditions for the violation-condition location).
 *
 * CPAchecker builds this from the paths of its ARG that end in a target state - for a block, these
 * are the block's paths, because inside a block the predicate analysis does not abstract (block
 * encoding with an abstraction only at the block end) - and conjoins the backward path formula of
 * each path with the violation condition it ended in; the conditions at the same program location
 * are then disjoined (`combineVcsByHash`). Theta's checkers return a single counterexample instead
 * of an ARG, so the paths are taken from the block itself: the result is the disjunction, over
 * every path from the block entry to a target, of the weakest existential precondition of that
 * path. As there is no abstraction inside a block either way, this is the same set of paths, except
 * that CPAchecker's ARG can already omit a path whose path formula became unsatisfiable together
 * with the start state. Since violation conditions never include the precondition, this only makes
 * the condition carry more (harmless) disjuncts.
 *
 * Blocks are acyclic apart from a loop body that starts and ends at the loop head (where, as for
 * [extractBlockXcfa], the head is the entry the first time and the exit the second time). Edge
 * labels are handled with the usual weakest-precondition rules (`assume c` -> `c && φ`, `x := e` ->
 * `φ[e/x]`, `havoc x` -> `φ[a/x]` for a fresh auxiliary variable `a`, see [DssAuxVars]); any other
 * label (function calls, memory operations, ...) is not supported yet and throws.
 */
fun computeViolationCondition(
  block: Block,
  targets: Map<XcfaLocation, Expr<BoolType>>,
): Expr<BoolType> {
  val memo = HashMap<XcfaLocation, Expr<BoolType>>()
  val onStack = HashSet<XcfaLocation>()

  fun fromLocation(location: XcfaLocation): Expr<BoolType> {
    memo[location]?.let {
      return it
    }
    check(onStack.add(location)) {
      "Block ${block.id} contains a cycle through ${location.name}; violation conditions can only " +
        "be computed for acyclic blocks"
    }
    val disjuncts = mutableListOf<Expr<BoolType>>()
    targets[location]?.let(disjuncts::add)
    // The block ends at its final location; only the ghost edge to the violation-condition
    // location may be followed from there.
    for (edge in location.outgoingEdges) {
      if (edge !in block.edges) continue
      if (location == block.finalLocation && edge.metadata != GhostEdgeMetadata) continue
      disjuncts += weakestPrecondition(edge.label, fromLocation(edge.target))
    }
    onStack.remove(location)
    return or(disjuncts).also { memo[location] = it }
  }

  val entry = block.initialLocation
  val fromEntry =
    or(
      entry.outgoingEdges
        .filter { it in block.edges && it.metadata != GhostEdgeMetadata }
        .map { weakestPrecondition(it.label, fromLocation(it.target)) }
    )
  return DssAuxVars.canonicalize(ExprUtils.simplify(fromEntry))
}

/**
 * Whether [block] has a cycle that [computeViolationCondition] cannot handle, i.e., one other than
 * a loop body that starts and ends at the loop head. Only `SelfLoopAbsorbingDecomposition` creates
 * such blocks. Unlike there, the block's own edges leaving its final location are followed: only a
 * split loop head ([extractBlockXcfa]) stops the analysis at the final location, and such a block
 * can also end on its own loop.
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
 * The violation condition of a single path ([labels], from the block entry to a target, ending with
 * the edge that enters the target): the weakest existential precondition of reaching the target
 * along exactly this path. Theta-only, for blocks with an internal cycle ([hasInternalCycle]),
 * whose paths cannot all be enumerated: each condition covers one counterexample, and a predecessor
 * that refutes it excludes it from its postcondition, so the next counterexample takes another
 * path.
 */
fun computePathViolationCondition(labels: List<XcfaLabel>): Expr<BoolType> =
  DssAuxVars.canonicalize(
    ExprUtils.simplify(
      labels.foldRight<XcfaLabel, Expr<BoolType>>(True()) { label, post ->
        weakestPrecondition(label, post)
      }
    )
  )

private fun weakestPrecondition(label: XcfaLabel, post: Expr<BoolType>): Expr<BoolType> =
  if (post == False()) False()
  else
    when (label) {
      is NopLabel -> post
      is StmtLabel -> weakestPrecondition(label.stmt, post)
      is SequenceLabel -> label.labels.foldRight(post) { l, acc -> weakestPrecondition(l, acc) }
      is NondetLabel -> or(label.labels.map { weakestPrecondition(it, post) })
      else ->
        throw UnsupportedOperationException(
          "DSS cannot compute violation conditions over $label (${label.javaClass.simpleName})"
        )
    }

private fun weakestPrecondition(stmt: Stmt, post: Expr<BoolType>): Expr<BoolType> =
  if (post == False()) False()
  else
    when (stmt) {
      is SkipStmt -> post
      is AssumeStmt -> and(stmt.cond, post)
      is AssignStmt<*> -> substitute(post, stmt.varDecl, stmt.expr)
      is HavocStmt<*> ->
        substitute(post, stmt.varDecl, DssAuxVars.freshFor(post, stmt.varDecl.type).ref)
      is SequenceStmt -> stmt.stmts.foldRight(post) { s, acc -> weakestPrecondition(s, acc) }
      is NonDetStmt -> or(stmt.stmts.map { weakestPrecondition(it, post) })
      else ->
        throw UnsupportedOperationException(
          "DSS cannot compute violation conditions over $stmt (${stmt.javaClass.simpleName})"
        )
    }

private fun substitute(post: Expr<BoolType>, decl: VarDecl<*>, value: Expr<*>): Expr<BoolType> =
  BasicSubstitution.builder().put(decl, value).build().apply(post)

private fun and(cond: Expr<BoolType>, post: Expr<BoolType>): Expr<BoolType> =
  when {
    cond == True() -> post
    post == True() -> cond
    cond == False() -> False()
    else -> And(cond, post)
  }

/**
 * Disjunction that factors out a shared continuation: the branches of a block typically end in the
 * same condition (`(c1 && φ) || (c2 && φ)`, e.g. two arms with the same update), and without
 * factoring every branch point would duplicate `φ`, doubling the condition with every loop
 * iteration it is propagated through. `(c1 || c2) && φ` keeps it linear.
 */
private fun or(disjuncts: List<Expr<BoolType>>): Expr<BoolType> {
  val relevant = disjuncts.filter { it != False() }.distinct()
  if (relevant.any { it == True() }) return True()
  if (relevant.size <= 1) return relevant.singleOrNull() ?: False()
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
        else -> listOf(and(or(heads), continuation))
      }
    }
  return if (factored.size == 1) factored.single() else Or(factored)
}
