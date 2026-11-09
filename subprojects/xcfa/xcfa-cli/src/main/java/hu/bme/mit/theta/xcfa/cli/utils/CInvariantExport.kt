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

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.LoopHead
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.ImplyExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.inttype.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mul
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ExactCPrinter
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.ContentItem
import hu.bme.mit.theta.xcfa.witnesses.Format
import hu.bme.mit.theta.xcfa.witnesses.Invariant
import hu.bme.mit.theta.xcfa.witnesses.InvariantType
import hu.bme.mit.theta.xcfa.witnesses.Location
import java.io.File
import java.math.BigInteger

private const val MAX_DISJUNCTS = 32
private const val MAX_LENGTH = 8192

/**
 * Loop invariants from the states of a single-threaded, fully inlined proof. All states at the
 * locations of a [LoopHead] are joined. Conjuncts over leftovers of inlined callees are dropped. A
 * loop is skipped if a pass removed its head, or if a state has another conjunct that is not over
 * the C variables in scope or that [ExactCPrinter] cannot print exactly: dropping it would keep the
 * join an invariant, but what remains may be too weak to prove inductively, and a validator would
 * spend its time on that instead of the property.
 */
internal fun LocationInvariants.loopInvariantContent(
  inputFile: File,
  parseContext: ParseContext,
  budgetMillis: Long = 10_000,
): List<ContentItem> {
  if (parseContext.multiThreading) return emptyList()
  val hasCalls =
    partitions.keys.any { loc ->
      loc.outgoingEdges.any { edge ->
        edge.getFlatLabels().any { it is InvokeLabel || it is StartLabel }
      }
    }
  if (hasCalls) return emptyList()

  val loops = LinkedHashMap<LoopHead, MutableList<ExprState>>()
  for ((loc, states) in partitions) {
    val head = (loc.metadata as? CMetaData)?.loopHead ?: continue
    loops.getOrPut(head) { mutableListOf() } += states
  }
  val deadline = System.currentTimeMillis() + budgetMillis
  return loops.mapNotNull { (head, states) ->
    if (!head.complete || System.currentTimeMillis() > deadline) return@mapNotNull null
    loopInvariant(head, states, inputFile, parseContext)
  }
}

private fun loopInvariant(
  head: LoopHead,
  states: List<ExprState>,
  inputFile: File,
  parseContext: ParseContext,
): ContentItem? {
  val names =
    head.variablesAtGuard.entries
      .filter { (_, decl) -> ExactCPrinter.cIntegerType(decl, parseContext) != null }
      .associate { (name, decl) -> decl to name }
  val printer = ExactCPrinter(names, parseContext)
  val disjuncts = LinkedHashSet<List<String>>()
  for (state in states) {
    if (state.isBottom) continue
    val simples = mutableListOf<Expr<BoolType>>()
    var infeasible = false
    var lostConjunct = false
    for (conjunct in conjunctsOf(state.toExpr())) {
      val outOfScope = ExprUtils.getVars(conjunct).filter { it !in names }
      if (outOfScope.isNotEmpty()) {
        lostConjunct =
          lostConjunct ||
            outOfScope.any {
              !it.name.contains("::") || it.name.startsWith(head.functionName + "::")
            }
        continue
      }
      val range = { decl: VarDecl<*> -> ExactCPrinter.typeRange(decl, parseContext) }
      for (simple in conjunctsOf(ExprUtils.simplify(pruneByRange(conjunct, range)))) {
        when (simple) {
          is TrueExpr -> {}
          is FalseExpr -> infeasible = true
          else -> simples += simple
        }
      }
    }
    if (infeasible) continue
    if (lostConjunct) return null
    val conjuncts = LinkedHashSet<String>()
    val merged = mergeBounds(simples) { ExactCPrinter.typeRange(it, parseContext) }
    for (simple in merged) conjuncts += printer.print(simple) ?: return null
    // a state that constrains nothing allows every value
    if (conjuncts.isEmpty()) return null
    disjuncts += conjuncts.toList()
  }
  if (disjuncts.isEmpty()) return null
  // a disjunct with all conjuncts of another one implies it
  disjuncts.retainAll(
    disjuncts.filter { d -> disjuncts.none { it.size < d.size && d.containsAll(it) } }.toSet()
  )

  fun conjunction(conjuncts: Collection<String>) = conjuncts.joinToString(" && ", "(", ")")
  // the conjuncts every state shares are implied by each of them
  val common = disjuncts.reduce { acc, next -> acc.filter { it in next } }
  val rests = disjuncts.map { conjuncts -> conjuncts.filter { it !in common } }
  val value =
    when {
      rests.any { it.isEmpty() } -> conjunction(common)
      disjuncts.size <= MAX_DISJUNCTS ->
        conjunction(common + rests.joinToString(" || ", "(", ")") { conjunction(it) })
      common.isNotEmpty() -> conjunction(common)
      else -> return null
    }.takeIf { it.length <= MAX_LENGTH }
      ?: conjunction(common).takeIf { common.isNotEmpty() && it.length <= MAX_LENGTH }
      ?: return null

  val loop = head.loop
  if (loop.lineNumberStart <= 0 || loop.colNumberStart < 0) return null
  return ContentItem(
    invariant =
      Invariant(
        type = InvariantType.LOOP_INVARIANT,
        location =
          Location(
            fileName = inputFile.name,
            line = loop.lineNumberStart,
            column = loop.colNumberStart + 1,
            function = head.functionName,
          ),
        value = value,
        format = Format.C_EXPRESSION,
      )
  )
}

/** A linear integer term: the sum of its coefficients times their variables, plus a constant. */
private data class Linear(val coefficients: Map<VarDecl<*>, BigInteger>, val constant: BigInteger) {
  operator fun plus(other: Linear): Linear {
    val sum = LinkedHashMap(coefficients)
    other.coefficients.forEach { (decl, k) -> sum.merge(decl, k, BigInteger::add) }
    sum.values.removeIf { it.signum() == 0 }
    return Linear(sum, constant + other.constant)
  }

  operator fun times(factor: BigInteger) =
    if (factor.signum() == 0) Linear(emptyMap(), BigInteger.ZERO)
    else Linear(coefficients.mapValues { it.value * factor }, constant * factor)

  operator fun minus(other: Linear) = this + other * BigInteger.ONE.negate()
}

private fun linear(e: Expr<*>): Linear? =
  when (e) {
    is IntLitExpr -> Linear(emptyMap(), e.value)
    is RefExpr<*> ->
      (e.decl as? VarDecl<*>)?.let { Linear(mapOf(it to BigInteger.ONE), BigInteger.ZERO) }
    is IntPosExpr -> linear(e.op)
    is IntNegExpr -> linear(e.op)?.times(BigInteger.ONE.negate())
    is IntAddExpr -> e.ops.map { linear(it) ?: return null }.reduceOrNull(Linear::plus)
    is IntSubExpr -> linear(e.leftOp)?.let { l -> linear(e.rightOp)?.let { r -> l - r } }
    is IntMulExpr -> {
      val factors = e.ops.map { linear(it) ?: return null }
      val nonConstant = factors.filter { it.coefficients.isNotEmpty() }
      val constant =
        factors
          .filter { it.coefficients.isEmpty() }
          .fold(BigInteger.ONE) { acc, f -> acc * f.constant }
      when (nonConstant.size) {
        0 -> Linear(emptyMap(), constant)
        1 -> nonConstant.single() * constant
        else -> null
      }
    }
    else -> null
  }

/** The linear term that is at least zero exactly when the integer comparison [e] holds. */
private fun lowerBound(e: Expr<*>): Linear? {
  fun diff(l: Expr<*>, r: Expr<*>, offset: Long = 0): Linear? =
    linear(l)?.let { a ->
      linear(r)?.let { b -> a - b + Linear(emptyMap(), BigInteger.valueOf(offset)) }
    }
  return when (e) {
    is IntGeqExpr -> diff(e.leftOp, e.rightOp)
    is IntLeqExpr -> diff(e.rightOp, e.leftOp)
    is IntGtExpr -> diff(e.leftOp, e.rightOp, -1)
    is IntLtExpr -> diff(e.rightOp, e.leftOp, -1)
    is NotExpr ->
      when (val op = e.op) {
        is IntGeqExpr -> diff(op.rightOp, op.leftOp, -1)
        is IntLeqExpr -> diff(op.leftOp, op.rightOp, -1)
        is IntGtExpr -> diff(op.rightOp, op.leftOp)
        is IntLtExpr -> diff(op.leftOp, op.rightOp)
        else -> null
      }
    else -> null
  }
}

@Suppress("UNCHECKED_CAST")
private fun sumOf(coefficients: Map<VarDecl<*>, BigInteger>, constant: BigInteger): Expr<IntType> {
  val ops =
    coefficients.map { (decl, k) ->
      val ref = decl.ref as Expr<IntType>
      if (k == BigInteger.ONE) ref else Mul(Int(k), ref)
    } + listOfNotNull(constant.takeIf { it.signum() != 0 }?.let { Int(it) })
  return when (ops.size) {
    0 -> Int(BigInteger.ZERO)
    1 -> ops.single()
    else -> Add(ops)
  }
}

/**
 * [conjuncts] with their linear bounds reduced: only the tightest bound on each term stays, two
 * opposite bounds become an equality, and bounds that the [range] of each variable already implies
 * are dropped. Validators can confirm `a == b` where they cannot confirm the same fact as `a <= b
 * && b <= a`, and the range checks of the overflow property tell them nothing.
 */
internal fun mergeBounds(
  conjuncts: List<Expr<BoolType>>,
  range: (VarDecl<*>) -> Pair<BigInteger, BigInteger>?,
): List<Expr<BoolType>> {
  val tightest = LinkedHashMap<Map<VarDecl<*>, BigInteger>, BigInteger>()
  val others =
    conjuncts
      .map { (it as? OrExpr)?.let(::unionBound) ?: it }
      .filter { conjunct ->
        val bound = lowerBound(conjunct)
        if (bound == null || bound.coefficients.isEmpty()) true
        else {
          tightest.merge(bound.coefficients, bound.constant, BigInteger::min)
          false
        }
      }
  val done = HashSet<Map<VarDecl<*>, BigInteger>>()
  val bounds = mutableListOf<Expr<BoolType>>()
  for ((coefficients, constant) in tightest) {
    if (!done.add(coefficients)) continue
    val opposite = coefficients.mapValues { it.value.negate() }
    val equal = tightest[opposite] == constant.negate()
    if (equal) done += opposite else if (alwaysHolds(coefficients, constant, range)) continue
    bounds += comparison(coefficients, constant, equal)
  }
  return others + bounds
}

/**
 * [expr] with the bounds inside it that the [range] of each variable decides replaced by their
 * value, so `!(1 <= i && n <= INT_MAX)` can simplify to `!(1 <= i)`. The range checks of the
 * overflow property end up nested like this.
 */
internal fun pruneByRange(
  expr: Expr<BoolType>,
  range: (VarDecl<*>) -> Pair<BigInteger, BigInteger>?,
): Expr<BoolType> =
  when (expr) {
    is NotExpr -> Not(pruneByRange(expr.op, range))
    is AndExpr -> And(expr.ops.map { pruneByRange(it, range) })
    is OrExpr -> Or(expr.ops.map { pruneByRange(it, range) })
    is IffExpr -> Iff(pruneByRange(expr.leftOp, range), pruneByRange(expr.rightOp, range))
    is ImplyExpr -> Imply(pruneByRange(expr.leftOp, range), pruneByRange(expr.rightOp, range))
    else -> {
      val bound = lowerBound(expr)
      when {
        bound == null || bound.coefficients.isEmpty() -> expr
        alwaysHolds(bound.coefficients, bound.constant, range) -> True()
        alwaysHolds(
          bound.coefficients.mapValues { it.value.negate() },
          bound.constant.negate().dec(),
          range,
        ) -> False()
        else -> expr
      }
    }
  }

/** Whether `term + constant >= 0` holds for all values in the [range] of each variable. */
private fun alwaysHolds(
  coefficients: Map<VarDecl<*>, BigInteger>,
  constant: BigInteger,
  range: (VarDecl<*>) -> Pair<BigInteger, BigInteger>?,
): Boolean {
  var min = constant
  for ((decl, k) in coefficients) {
    val (low, high) = range(decl) ?: return false
    min += k * (if (k.signum() > 0) low else high)
  }
  return min.signum() >= 0
}

/** `term + constant == 0` if [equal], otherwise `term + constant >= 0`, without negative terms. */
private fun comparison(
  coefficients: Map<VarDecl<*>, BigInteger>,
  constant: BigInteger,
  equal: Boolean,
): Expr<BoolType> {
  val positive = coefficients.filterValues { it.signum() > 0 }
  val negative = coefficients.filterValues { it.signum() < 0 }.mapValues { it.value.negate() }
  val left = sumOf(positive, constant.max(BigInteger.ZERO))
  val right = sumOf(negative, constant.negate().max(BigInteger.ZERO))
  return if (equal) Eq(left, right)
  else if (positive.isEmpty()) Leq(right, left) else Geq(left, right)
}

/**
 * The single bound equal to [or], if its operands are adjoining ranges of one linear term, such as
 * `a == b || a > b` for `a >= b`.
 */
private fun unionBound(or: OrExpr): Expr<BoolType>? {
  class Range(val min: BigInteger?, val max: BigInteger?)
  var term: Map<VarDecl<*>, BigInteger>? = null
  val ranges =
    or.ops.map { op ->
      val equality =
        (op as? IntEqExpr)?.let { eq ->
          linear(eq.leftOp)?.let { l -> linear(eq.rightOp)?.let { l - it } }
        }
      val bound = equality ?: lowerBound(op) ?: return null
      val base = term ?: bound.coefficients.also { term = it }
      val flipped = bound.coefficients == base.mapValues { it.value.negate() }
      if (base.isEmpty() || (!flipped && bound.coefficients != base)) return null
      val value = if (flipped) bound.constant else bound.constant.negate()
      when {
        equality != null -> Range(value, value)
        flipped -> Range(null, value)
        else -> Range(value, null)
      }
    }
  val lowest = ranges.filter { it.max == null }.mapNotNull { it.min }.minOrNull()
  val highest = ranges.filter { it.min == null }.mapNotNull { it.max }.maxOrNull()
  if ((lowest == null) == (highest == null)) return null
  val points = ranges.filter { it.min != null && it.max != null }.map { it.min!! }.distinct()
  // the points must extend the open range without a gap
  return if (lowest != null) {
    var min: BigInteger = lowest
    for (point in points.sortedDescending()) if (point == min.dec()) min = point
    else if (point < min) return null
    comparison(term!!, min.negate(), false)
  } else {
    var max: BigInteger = highest!!
    for (point in points.sorted()) if (point == max.inc()) max = point
    else if (point > max) return null
    comparison(term!!.mapValues { it.value.negate() }, max, false)
  }
}

/** The conjuncts of [expr] with nested conjunctions flattened, in order. */
private fun conjunctsOf(expr: Expr<BoolType>): List<Expr<BoolType>> =
  if (expr is AndExpr) expr.ops.flatMap(::conjunctsOf) else listOf(expr)
