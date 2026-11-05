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
import hu.bme.mit.theta.core.type.anytype.IteExpr
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
import hu.bme.mit.theta.core.type.booltype.XorExpr
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.inttype.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mul
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
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
 * the C variables in scope or that [CInvariantPrinter] cannot print exactly: dropping it would keep
 * the join an invariant, but what remains may be too weak to prove inductively, and a validator
 * would spend its time on that instead of the property.
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
      .filter { (_, decl) -> CInvariantPrinter.cIntegerType(decl, parseContext) != null }
      .associate { (name, decl) -> decl to name }
  val printer = CInvariantPrinter(names, parseContext)
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
      val range = { decl: VarDecl<*> -> CInvariantPrinter.typeRange(decl, parseContext) }
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
    val merged = mergeBounds(simples) { CInvariantPrinter.typeRange(it, parseContext) }
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

/**
 * Prints a Theta expression as a C expression with the same value, or null if it cannot do so
 * exactly. Integers are evaluated in `long long` and bounded, so the C evaluation cannot overflow.
 * Bitvectors are evaluated as their unsigned value in `unsigned long long` and masked to their
 * width, where wraparound is defined; signed comparisons flip the sign bit.
 */
internal class CInvariantPrinter(
  private val names: Map<VarDecl<*>, String>,
  private val parseContext: ParseContext,
) {

  companion object {
    private val LLONG_MIN = BigInteger.valueOf(Long.MIN_VALUE)
    private val LLONG_MAX = BigInteger.valueOf(Long.MAX_VALUE)

    /**
     * The C integer type the frontend gave [decl], unless it is a pointer or wider than 64 bits.
     */
    fun cIntegerType(decl: VarDecl<*>, parseContext: ParseContext): CInteger? {
      // not CComplexType.getType: without metadata it guesses a type from the Theta type
      val type =
        when (val cType = parseContext.metadata.getMetadataValue(decl.ref, "cType").orElse(null)) {
          is CComplexType -> cType
          is CSimpleType -> cType.actualType
          else -> null
        }
      return (type as? CInteger)?.takeIf { it !is CPointer && it.width() in 1..64 }
    }

    /** The values of the C integer type of [decl], see [cIntegerType]. */
    fun typeRange(decl: VarDecl<*>, parseContext: ParseContext): Pair<BigInteger, BigInteger>? {
      val type = cIntegerType(decl, parseContext) ?: return null
      val width = type.width()
      return if (type.isSsigned)
        BigInteger.ONE.shiftLeft(width - 1).negate() to BigInteger.ONE.shiftLeft(width - 1).dec()
      else BigInteger.ZERO to BigInteger.ONE.shiftLeft(width).dec()
    }

    private fun mask(width: Int): String = BigInteger.ONE.shiftLeft(width).dec().toString() + "ULL"

    private fun signBit(width: Int): String = BigInteger.ONE.shiftLeft(width - 1).toString() + "ULL"
  }

  private class IntTerm(val text: String, val min: BigInteger, val max: BigInteger)

  fun print(expr: Expr<BoolType>): String? = bool(expr)

  private fun bool(e: Expr<*>): String? =
    when (e) {
      is TrueExpr -> "1"
      is FalseExpr -> "0"
      is NotExpr -> bool(e.op)?.let { "!$it" }
      is AndExpr -> nary(e.ops, " && ", "1")
      is OrExpr -> nary(e.ops, " || ", "0")
      is ImplyExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l || $r)" } }
      is IffExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l == !$r)" } }
      is XorExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l != !$r)" } }
      is IteExpr<*> -> if (e.type is BoolType) ite(e.cond, bool(e.then), bool(e.`else`)) else null
      is IntEqExpr -> intCompare(e.leftOp, "==", e.rightOp)
      is IntNeqExpr -> intCompare(e.leftOp, "!=", e.rightOp)
      is IntLtExpr -> intCompare(e.leftOp, "<", e.rightOp)
      is IntLeqExpr -> intCompare(e.leftOp, "<=", e.rightOp)
      is IntGtExpr -> intCompare(e.leftOp, ">", e.rightOp)
      is IntGeqExpr -> intCompare(e.leftOp, ">=", e.rightOp)
      is BvEqExpr -> bvCompare(e.leftOp, "==", e.rightOp)
      is BvNeqExpr -> bvCompare(e.leftOp, "!=", e.rightOp)
      is BvULtExpr -> bvCompare(e.leftOp, "<", e.rightOp)
      is BvULeqExpr -> bvCompare(e.leftOp, "<=", e.rightOp)
      is BvUGtExpr -> bvCompare(e.leftOp, ">", e.rightOp)
      is BvUGeqExpr -> bvCompare(e.leftOp, ">=", e.rightOp)
      is BvSLtExpr -> bvCompare(e.leftOp, "<", e.rightOp, signed = true)
      is BvSLeqExpr -> bvCompare(e.leftOp, "<=", e.rightOp, signed = true)
      is BvSGtExpr -> bvCompare(e.leftOp, ">", e.rightOp, signed = true)
      is BvSGeqExpr -> bvCompare(e.leftOp, ">=", e.rightOp, signed = true)
      else -> null
    }

  private fun nary(ops: List<Expr<*>>, separator: String, empty: String): String? {
    if (ops.isEmpty()) return empty
    val printed = ops.map { bool(it) ?: return null }
    return printed.joinToString(separator, "(", ")")
  }

  private fun ite(cond: Expr<*>, then: String?, otherwise: String?): String? =
    bool(cond)?.let { c -> then?.let { t -> otherwise?.let { o -> "($c ? $t : $o)" } } }

  private fun intCompare(left: Expr<*>, op: String, right: Expr<*>): String? {
    val l = int(left) ?: return null
    val r = int(right) ?: return null
    return "(${l.text} $op ${r.text})"
  }

  /** A `long long` term, or null if a value on the way may leave the range of `long long`. */
  private fun intTerm(text: String, min: BigInteger, max: BigInteger): IntTerm? =
    if (min >= LLONG_MIN && max <= LLONG_MAX) IntTerm(text, min, max) else null

  private fun int(e: Expr<*>): IntTerm? =
    when (e) {
      is IntLitExpr -> {
        val v = e.value
        val text =
          if (v == LLONG_MIN) "(-9223372036854775807LL - 1)"
          else if (v.signum() < 0) "(${v}LL)" else "${v}LL"
        intTerm(text, v, v)
      }
      is RefExpr<*> -> {
        val decl = e.decl as? VarDecl<*> ?: return null
        val name = names[decl] ?: return null
        val (min, max) = typeRange(decl, parseContext) ?: return null
        intTerm("((long long)$name)", min, max)
      }
      is IntPosExpr -> int(e.op)
      is IntNegExpr -> int(e.op)?.let(::neg)
      is IntAddExpr -> sum(e.ops)
      is IntSubExpr -> {
        val l = int(e.leftOp) ?: return null
        val r = int(e.rightOp) ?: return null
        sub(l, r)
      }
      is IntMulExpr ->
        negated(e)?.let { positive -> int(positive)?.let(::neg) }
          ?: e.ops.map { int(it) ?: return null }.reduceOrNull { a, b -> mul(a, b) ?: return null }
      is IteExpr<*> -> {
        val c = bool(e.cond) ?: return null
        val t = int(e.then) ?: return null
        val o = int(e.`else`) ?: return null
        intTerm("($c ? ${t.text} : ${o.text})", t.min.min(o.min), t.max.max(o.max))
      }
      else -> null
    }

  /**
   * The term `t` if [e] is `-t` or has a negative constant factor. Solvers can be far slower on a
   * multiplication by a negative constant than on the equal subtraction, so those are not printed.
   */
  private fun negated(e: Expr<*>): Expr<IntType>? =
    when (e) {
      is IntNegExpr -> e.op
      is IntLitExpr -> if (e.value.signum() < 0) Int(e.value.negate()) else null
      is IntMulExpr -> {
        val factor = e.ops.filterIsInstance<IntLitExpr>().singleOrNull { it.value.signum() < 0 }
        val rest = e.ops.filter { it !== factor }
        when {
          factor == null -> null
          factor.value != BigInteger.ONE.negate() -> Mul(listOf(Int(factor.value.negate())) + rest)
          rest.size == 1 -> rest.single()
          else -> Mul(rest)
        }
      }
      else -> null
    }

  /** The sum of [ops], with the positive terms first and the negative ones subtracted. */
  private fun sum(ops: List<Expr<IntType>>): IntTerm? {
    val (subtracted, added) = ops.partition { negated(it) != null }
    var acc = added.map { int(it) ?: return null }.reduceOrNull { a, b -> add(a, b) ?: return null }
    for (op in subtracted) {
      val term = int(negated(op)!!) ?: return null
      acc = (if (acc == null) neg(term) else sub(acc, term)) ?: return null
    }
    return acc
  }

  private fun add(a: IntTerm, b: IntTerm) =
    intTerm("(${a.text} + ${b.text})", a.min + b.min, a.max + b.max)

  private fun sub(a: IntTerm, b: IntTerm) =
    intTerm("(${a.text} - ${b.text})", a.min - b.max, a.max - b.min)

  private fun neg(a: IntTerm) = intTerm("(-${a.text})", a.max.negate(), a.min.negate())

  private fun mul(a: IntTerm, b: IntTerm): IntTerm? {
    val products = listOf(a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max)
    return intTerm("(${a.text} * ${b.text})", products.min(), products.max())
  }

  private fun bvCompare(
    left: Expr<*>,
    op: String,
    right: Expr<*>,
    signed: Boolean = false,
  ): String? {
    val width = (left.type as BvType).size
    val l = bv(left) ?: return null
    val r = bv(right) ?: return null
    return if (signed) "(($l ^ ${signBit(width)}) $op ($r ^ ${signBit(width)}))" else "($l $op $r)"
  }

  /** An `unsigned long long` expression whose value is the unsigned value of [e]. */
  private fun bv(e: Expr<*>): String? {
    val width = (e.type as? BvType)?.size ?: return null
    if (width !in 1..64) return null
    fun masked(text: String) = if (width == 64) text else "($text & ${mask(width)})"
    return when (e) {
      is BvLitExpr -> "${BvUtils.unsignedBvLitExprToBigInteger(e)}ULL"
      is RefExpr<*> -> {
        val decl = e.decl as? VarDecl<*> ?: return null
        val name = names[decl] ?: return null
        val type = cIntegerType(decl, parseContext) ?: return null
        if (type.width() != width) return null
        if (!type.isSsigned || width == 64) "((unsigned long long)$name)"
        else {
          val unsigned =
            when (width) {
              8 -> "unsigned char"
              16 -> "unsigned short"
              32 -> "unsigned int"
              else -> return null
            }
          "((unsigned long long)($unsigned)$name)"
        }
      }
      is BvPosExpr -> bv(e.op)
      is BvSignChangeExpr -> bv(e.op)
      is BvZExtExpr -> bv(e.op)
      is BvSExtExpr -> {
        val from = e.op.type.size
        val a = bv(e.op) ?: return null
        masked("((($a ^ ${signBit(from)}) - ${signBit(from)}))")
      }
      is BvExtractExpr -> {
        val a = bv(e.bitvec) ?: return null
        val from = e.from.value.toInt()
        masked(if (from == 0) a else "($a >> $from)")
      }
      is BvConcatExpr ->
        e.ops
          .map { (bv(it) ?: return null) to (it.type as BvType).size }
          .reduceOrNull { (acc, _), (next, nextWidth) ->
            "(($acc << $nextWidth) | $next)" to nextWidth
          }
          ?.first
      is BvAddExpr -> bvNary(e.ops, " + ")?.let(::masked)
      is BvMulExpr -> bvNary(e.ops, " * ")?.let(::masked)
      is BvSubExpr -> {
        val l = bv(e.leftOp) ?: return null
        val r = bv(e.rightOp) ?: return null
        masked("($l - $r)")
      }
      is BvNegExpr -> bv(e.op)?.let { masked("(0ULL - $it)") }
      is BvNotExpr -> bv(e.op)?.let { masked("(~$it)") }
      is BvAndExpr -> bvNary(e.ops, " & ")
      is BvOrExpr -> bvNary(e.ops, " | ")
      is BvXorExpr -> bvNary(e.ops, " ^ ")
      // shifting by the width or more is undefined in C, but zero in SMT
      is BvShiftLeftExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b < ${width}ULL ? ${masked("($a << $b)")} : 0ULL)"
      }
      is BvLogicShiftRightExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b < ${width}ULL ? ($a >> $b) : 0ULL)"
      }
      // division by zero is undefined in C, but defined in SMT
      is BvUDivExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b == 0ULL ? ${mask(width)} : ($a / $b))"
      }
      is BvURemExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b == 0ULL ? $a : ($a % $b))"
      }
      is IteExpr<*> -> {
        val c = bool(e.cond) ?: return null
        val t = bv(e.then) ?: return null
        val o = bv(e.`else`) ?: return null
        "($c ? $t : $o)"
      }
      else -> null
    }
  }

  private fun bvNary(ops: List<Expr<*>>, separator: String): String? =
    if (ops.isEmpty()) null else ops.map { bv(it) ?: return null }.joinToString(separator, "(", ")")
}
