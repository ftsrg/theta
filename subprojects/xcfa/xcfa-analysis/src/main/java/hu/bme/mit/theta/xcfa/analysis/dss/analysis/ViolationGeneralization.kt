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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntAddExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mul
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr
import hu.bme.mit.theta.core.type.inttype.IntGtExpr
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLtExpr
import hu.bme.mit.theta.core.type.inttype.IntMulExpr
import hu.bme.mit.theta.core.type.inttype.IntNegExpr
import hu.bme.mit.theta.core.type.inttype.IntPosExpr
import hu.bme.mit.theta.core.type.inttype.IntSubExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import java.math.BigInteger

/**
 * GSpacer's global guidance (Krishnan et al., FMSD 2024) for violation conditions: cubes of one
 * shape whose numbers keep drifting are covered by their widened convex hull, or by the cube
 * without its drifting literals. The result is a *may* condition, only ever a probe target.
 */
class ViolationGeneralizer(private val gas: Int, private val minClusterSize: Int = 2) {

  init {
    require(gas > 0 && minClusterSize >= 2)
  }

  /** A probe target for the conditions received together, from the clusters [keys]. */
  class Generalization
  internal constructor(
    val condition: Expr<BoolType>,
    internal val candidates: Map<ClusterKey, Expr<BoolType>>,
  )

  internal data class ClusterKey(val sender: String, val shape: List<Any>)

  /** Distinct bound vectors per shape, in arrival order. */
  private val clusters = HashMap<ClusterKey, MutableList<List<BigInteger>>>()
  private val gasLeft = HashMap<ClusterKey, Int>()
  private val failedCandidates = HashMap<ClusterKey, MutableSet<Expr<BoolType>>>()

  fun record(sender: String, condition: Expr<BoolType>) {
    for (cube in normalizedCubes(condition) ?: return) {
      val points = clusters.getOrPut(ClusterKey(sender, cube.shape)) { mutableListOf() }
      if (cube.bounds !in points) points += cube.bounds
    }
  }

  /**
   * A generalization of the [received] conditions, or null if no cluster qualifies. [isUnsat]
   * decides the usefulness checks; an undecided query must throw, which skips the generalization.
   */
  fun generalize(
    received: List<Pair<String, Expr<BoolType>>>,
    isUnsat: (Expr<BoolType>) -> Boolean,
  ): Generalization? {
    val exact = Or(received.map { it.second })
    val chosen = LinkedHashMap<ClusterKey, Expr<BoolType>>()
    for ((sender, condition) in received) {
      for (cube in normalizedCubes(condition) ?: continue) {
        val key = ClusterKey(sender, cube.shape)
        if (key in chosen || gasLeft.getOrPut(key) { gas } <= 0) continue
        val points = clusters[key] ?: continue
        if (points.size < minClusterSize) continue
        val failed = failedCandidates[key].orEmpty()
        candidates(cube, points)
          .firstOrNull { it !in failed && isUseful(it, exact, isUnsat) }
          ?.let { chosen[key] = it }
      }
    }
    if (chosen.isEmpty()) return null
    return Generalization(DssAuxVars.canonicalize(Or(chosen.values)), chosen)
  }

  /** [generalization] was reached from a start state: its clusters lose gas. */
  fun failed(generalization: Generalization) {
    for ((key, candidate) in generalization.candidates) {
      gasLeft.merge(key, gas - 1) { left, _ -> left - 1 }
      failedCandidates.getOrPut(key) { hashSetOf() } += candidate
    }
  }

  private fun isUseful(
    candidate: Expr<BoolType>,
    exact: Expr<BoolType>,
    isUnsat: (Expr<BoolType>) -> Boolean,
  ): Boolean = !isUnsat(Not(candidate)) && !isUnsat(And(candidate, Not(exact)))

  private fun candidates(cube: Cube, points: List<List<BigInteger>>): List<Expr<BoolType>> {
    val varying = cube.bounds.indices.filter { j -> points.any { it[j] != points[0][j] } }
    if (varying.isEmpty()) return emptyList()
    return listOfNotNull(widenedHull(cube, points, varying), withoutDrifting(cube, varying))
      .filter { it != True() }
      .distinct()
  }
}

// ---------------------------------------------------------------------------------------------
// Cubes in linear normal form

/** `sum(terms) <= bound`, or `= bound`: terms ordered by [termOrder], with nonzero coefficients. */
internal data class LinearLiteral(
  val terms: List<Pair<VarDecl<*>, BigInteger>>,
  val equality: Boolean,
  val bound: BigInteger,
)

/** A conjunction of [LinearLiteral]s and opaque literals, in a canonical order. */
internal class Cube(val linear: List<LinearLiteral>, val opaque: List<Expr<BoolType>>) {
  val shape: List<Any> = linear.map { it.terms to it.equality } + opaque
  val bounds: List<BigInteger> = linear.map { it.bound }

  fun toExpr(): Expr<BoolType> = And(linear.map { it.toExpr() } + opaque)
}

private val termOrder = compareBy<VarDecl<*>>({ it.name }, { System.identityHashCode(it) })

/** The cubes of [condition]'s DNF in normal form (false ones dropped), or null above [maxCubes]. */
internal fun normalizedCubes(condition: Expr<BoolType>, maxCubes: Int = 16): List<Cube>? =
  dnf(ExprUtils.simplify(condition), maxCubes)?.mapNotNull(::normalizeCube)

private fun dnf(expr: Expr<BoolType>, maxCubes: Int): List<List<Expr<BoolType>>>? =
  when {
    expr == True() -> listOf(emptyList())
    expr == False() -> emptyList()
    expr is OrExpr ->
      expr.ops.map { dnf(it, maxCubes) ?: return null }.flatten().takeIf { it.size <= maxCubes }
    expr is AndExpr ->
      expr.ops.fold(listOf(emptyList<Expr<BoolType>>())) { acc, op ->
        val cubes = dnf(op, maxCubes) ?: return null
        if (acc.size * cubes.size > maxCubes) return null
        acc.flatMap { prefix -> cubes.map { prefix + it } }
      }
    else -> listOf(listOf(expr))
  }

private sealed interface Literal

private data class LinearLit(val literal: LinearLiteral) : Literal

private data class OpaqueLit(val expr: Expr<BoolType>) : Literal

private object TrueLit : Literal

private object FalseLit : Literal

/**
 * Normalizes the conjunction [literals]: equalities `x = c` are substituted into the other
 * literals, and literals implied by another one of the same terms are dropped; null if false.
 */
internal fun normalizeCube(literals: List<Expr<BoolType>>): Cube? {
  var current = literals.map(::parseLiteral)
  val substituted = HashSet<VarDecl<*>>()
  while (true) {
    if (current.any { it == FalseLit }) return null
    current = current.filter { it != TrueLit }
    val definition =
      current.firstNotNullOfOrNull { lit ->
        (lit as? LinearLit)?.literal?.takeIf {
          it.equality && it.terms.size == 1 && it.terms[0].first !in substituted
        }
      } ?: break
    val (variable, coefficient) = definition.terms.single()
    check(coefficient == BigInteger.ONE)
    substituted += variable
    current =
      current.map { lit ->
        if (lit is LinearLit && lit.literal == definition) lit
        else substitute(lit, variable, definition.bound)
      }
  }
  // An auxiliary variable is existential: once substituted, its definition says nothing more
  current =
    current.filterNot { lit ->
      lit is LinearLit &&
        lit.literal.equality &&
        lit.literal.terms.singleOrNull()?.first?.let {
          it in substituted && DssAuxVars.isAux(it)
        } == true
    }
  val linear = mergeBounds(current.filterIsInstance<LinearLit>().map { it.literal }) ?: return null
  val opaque = current.filterIsInstance<OpaqueLit>().map { it.expr }.distinct()
  return Cube(
    linear.sortedWith(compareBy({ it.terms.toString() }, { it.equality })),
    opaque.sortedBy { it.toString() },
  )
}

private fun substitute(literal: Literal, variable: VarDecl<*>, value: BigInteger): Literal =
  when (literal) {
    is LinearLit -> {
      val coefficient = literal.literal.terms.firstOrNull { it.first == variable }?.second
      if (coefficient == null) literal
      else
        normalizeLinear(
          literal.literal.terms.filter { it.first != variable },
          literal.literal.equality,
          literal.literal.bound - coefficient * value,
        )
    }
    is OpaqueLit -> {
      if (variable !in ExprUtils.getVars(literal.expr)) literal
      else {
        @Suppress("UNCHECKED_CAST")
        val substitution =
          BasicSubstitution.builder().put(variable as VarDecl<IntType>, Int(value)).build()
        parseLiteral(ExprUtils.simplify(substitution.apply(literal.expr)))
      }
    }
    else -> literal
  }

/** Keeps the tightest bound per terms; `t <= b` and `-t <= -b` become `t = b`. Null if false. */
private fun mergeBounds(literals: List<LinearLiteral>): List<LinearLiteral>? {
  val equalities = HashMap<List<Pair<VarDecl<*>, BigInteger>>, BigInteger>()
  val upper = LinkedHashMap<List<Pair<VarDecl<*>, BigInteger>>, BigInteger>()
  for (literal in literals) {
    if (literal.equality) {
      val old = equalities.put(literal.terms, literal.bound)
      if (old != null && old != literal.bound) return null
    } else {
      upper.merge(literal.terms, literal.bound, BigInteger::min)
    }
  }
  fun negated(terms: List<Pair<VarDecl<*>, BigInteger>>) = terms.map { (v, c) -> v to -c }
  // An equality is stored with a positive first coefficient, see normalizeLinear
  fun equalityValue(terms: List<Pair<VarDecl<*>, BigInteger>>): BigInteger? =
    equalities[terms] ?: equalities[negated(terms)]?.negate()
  val result = mutableListOf<LinearLiteral>()
  equalities.forEach { (terms, bound) -> result += LinearLiteral(terms, true, bound) }
  val done = HashSet<List<Pair<VarDecl<*>, BigInteger>>>()
  for ((terms, bound) in upper) {
    if (terms in done) continue
    val value = equalityValue(terms)
    if (value != null) {
      if (value > bound) return null
      continue
    }
    val lower = upper[negated(terms)]?.negate()
    if (lower != null) {
      done += negated(terms)
      when {
        lower > bound -> return null
        lower == bound -> {
          result += (normalizeLinear(terms, true, bound) as LinearLit).literal
          continue
        }
        else -> result += LinearLiteral(negated(terms), false, -lower)
      }
    }
    result += LinearLiteral(terms, false, bound)
  }
  return result
}

private fun parseLiteral(expr: Expr<BoolType>): Literal {
  if (expr == True()) return TrueLit
  if (expr == False()) return FalseLit
  val negated = expr is NotExpr
  val atom = if (expr is NotExpr) expr.op else expr
  fun difference(left: Expr<*>, right: Expr<*>): LinearTerm? =
    linearTerm(left)?.let { l -> linearTerm(right)?.let { r -> l - r } }
  // `left - right rel 0`, as (difference, equality, strict)
  val relation: Triple<LinearTerm, Boolean, Boolean>? =
    when (atom) {
      is IntLeqExpr -> difference(atom.leftOp, atom.rightOp)?.let { Triple(it, false, false) }
      is IntLtExpr -> difference(atom.leftOp, atom.rightOp)?.let { Triple(it, false, true) }
      is IntGeqExpr -> difference(atom.rightOp, atom.leftOp)?.let { Triple(it, false, false) }
      is IntGtExpr -> difference(atom.rightOp, atom.leftOp)?.let { Triple(it, false, true) }
      is IntEqExpr -> difference(atom.leftOp, atom.rightOp)?.let { Triple(it, true, false) }
      else -> null
    }
  if (relation == null) return OpaqueLit(expr)
  val (term, equality, strict) = relation
  if (equality && negated) return OpaqueLit(expr)
  val terms = term.coefficients.entries.map { it.key to it.value }
  // t + c <= 0 is t <= -c; t + c < 0 is t <= -c - 1; not(t + c <= 0) is -t <= c - 1
  return when {
    equality -> normalizeLinear(terms, true, -term.constant)
    !negated -> normalizeLinear(terms, false, -term.constant - (if (strict) ONE else ZERO))
    else ->
      normalizeLinear(
        terms.map { (v, c) -> v to -c },
        false,
        term.constant - (if (strict) ZERO else ONE),
      )
  }
}

private val ONE = BigInteger.ONE
private val ZERO = BigInteger.ZERO

/** Divides by the gcd (rounding the bound down), so equal half-spaces are equal literals. */
private fun normalizeLinear(
  rawTerms: List<Pair<VarDecl<*>, BigInteger>>,
  equality: Boolean,
  bound: BigInteger,
): Literal {
  val terms =
    rawTerms
      .groupBy({ it.first }, { it.second })
      .mapValues { (_, cs) -> cs.fold(ZERO, BigInteger::add) }
      .filterValues { it.signum() != 0 }
      .entries
      .map { it.key to it.value }
      .sortedWith(compareBy(termOrder) { it.first })
  if (terms.isEmpty()) {
    val holds = if (equality) bound.signum() == 0 else bound.signum() >= 0
    return if (holds) TrueLit else FalseLit
  }
  val gcd = terms.fold(ZERO) { acc, (_, c) -> acc.gcd(c) }
  if (equality) {
    if (bound.mod(gcd).signum() != 0) return FalseLit
    val sign = if (terms[0].second.signum() < 0) gcd.negate() else gcd
    return LinearLit(LinearLiteral(terms.map { (v, c) -> v to c / sign }, true, bound / sign))
  }
  return LinearLit(LinearLiteral(terms.map { (v, c) -> v to c / gcd }, false, floorDiv(bound, gcd)))
}

private fun floorDiv(a: BigInteger, b: BigInteger): BigInteger {
  val (q, r) = a.divideAndRemainder(b)
  return if (r.signum() != 0 && (r.signum() < 0) != (b.signum() < 0)) q - ONE else q
}

private class LinearTerm(val coefficients: Map<VarDecl<*>, BigInteger>, val constant: BigInteger) {
  operator fun plus(other: LinearTerm) =
    LinearTerm(
      (coefficients.keys + other.coefficients.keys).associateWith {
        (coefficients[it] ?: ZERO) + (other.coefficients[it] ?: ZERO)
      },
      constant + other.constant,
    )

  operator fun times(factor: BigInteger) =
    LinearTerm(coefficients.mapValues { it.value * factor }, constant * factor)

  operator fun minus(other: LinearTerm) = this + other * ONE.negate()
}

private fun linearTerm(expr: Expr<*>): LinearTerm? =
  when (expr) {
    is IntLitExpr -> LinearTerm(emptyMap(), expr.value)
    is RefExpr<*> ->
      (expr.decl as? VarDecl<*>)
        ?.takeIf { it.type is IntType }
        ?.let { LinearTerm(mapOf(it to ONE), ZERO) }
    is IntAddExpr ->
      expr.ops.fold(LinearTerm(emptyMap(), ZERO)) { acc, op ->
        acc + (linearTerm(op) ?: return null)
      }
    is IntSubExpr ->
      linearTerm(expr.leftOp)?.let { l -> linearTerm(expr.rightOp)?.let { r -> l - r } }
    is IntNegExpr -> linearTerm(expr.op)?.times(ONE.negate())
    is IntPosExpr -> linearTerm(expr.op)
    is IntMulExpr -> {
      val factors = expr.ops.map { linearTerm(it) ?: return null }
      val variable = factors.filter { it.coefficients.values.any { c -> c.signum() != 0 } }
      if (variable.size > 1) null
      else {
        val constant = factors.filter { it !in variable }.fold(ONE) { acc, f -> acc * f.constant }
        (variable.singleOrNull() ?: LinearTerm(emptyMap(), ONE)) * constant
      }
    }
    else -> null
  }

internal fun LinearLiteral.toExpr(): Expr<BoolType> {
  @Suppress("UNCHECKED_CAST") fun ref(v: VarDecl<*>) = (v as VarDecl<IntType>).ref
  val single = terms.singleOrNull()
  if (single != null && single.second == ONE.negate() && !equality) {
    return Geq(ref(single.first), Int(bound.negate()))
  }
  val summands = terms.map { (v, c) -> if (c == ONE) ref(v) else Mul(Int(c), ref(v)) }
  val sum = summands.singleOrNull() ?: Add(summands)
  return if (equality) Eq(sum, Int(bound)) else Leq(sum, Int(bound))
}

// ---------------------------------------------------------------------------------------------
// Generalizing a cluster

/** [cube] without the literals whose bounds differ between the [varying] positions. */
private fun withoutDrifting(cube: Cube, varying: List<Int>): Expr<BoolType> =
  Cube(cube.linear.filterIndexed { j, _ -> j !in varying }, cube.opaque).toExpr()

/**
 * The convex hull of [points], widened along each direction they keep moving in, by Fourier-Motzkin
 * over the rationals. Null if no direction moves monotonically or the elimination grows too large.
 */
private fun widenedHull(
  cube: Cube,
  points: List<List<BigInteger>>,
  varying: List<Int>,
  maxConstraints: Int = 64,
): Expr<BoolType>? {
  val base = points[0].map { Rational.of(it) }
  val basis =
    rowReduce(points.drop(1).map { p -> varying.map { j -> Rational.of(p[j]) - base[j] } })
  if (basis.isEmpty()) return null
  // The coordinates of each point in the reduced basis can be read off at the pivot columns
  val pivots = basis.map { row -> row.indexOfFirst { it.signum != 0 } }
  val coordinates =
    points.map { p -> pivots.map { col -> Rational.of(p[varying[col]]) - base[varying[col]] } }
  val ranges =
    basis.indices.map { k ->
      val values = coordinates.map { it[k] }
      val increasing = values.zipWithNext().all { (a, b) -> a <= b } && values.last() > values[0]
      val decreasing = values.zipWithNext().all { (a, b) -> a >= b } && values.last() < values[0]
      Triple(
        values.min().takeUnless { decreasing },
        values.max().takeUnless { increasing },
        increasing || decreasing,
      )
    }
  if (ranges.none { it.third }) return null

  // sum(xs) + sum(ts * t) + constant (<= | =) 0
  val constraints = mutableListOf<Constraint>()
  cube.linear.forEachIndexed { j, literal ->
    val column = varying.indexOf(j)
    val ts =
      if (column < 0) emptyMap()
      else basis.indices.associateWith { k -> -basis[k][column] }.filterValues { it.signum != 0 }
    constraints +=
      Constraint(
        literal.terms.associate { (v, c) -> v to Rational.of(c) },
        ts,
        -(if (column < 0) Rational.of(literal.bound) else base[j]),
        literal.equality,
      )
  }
  ranges.forEachIndexed { k, (low, high, _) ->
    if (low != null) constraints += Constraint(emptyMap(), mapOf(k to -Rational.ONE), low, false)
    if (high != null) constraints += Constraint(emptyMap(), mapOf(k to Rational.ONE), -high, false)
  }
  var system: List<Constraint> = constraints
  for (k in basis.indices) {
    system = eliminate(system, k) ?: return null
    if (system.size > maxConstraints) return null
  }
  val literals = mutableListOf<Expr<BoolType>>()
  for (constraint in system) {
    when (val literal = constraint.toLiteral()) {
      is LinearLit -> literals += literal.literal.toExpr()
      FalseLit -> return null
      else -> {}
    }
  }
  return normalizeCube(literals + cube.opaque)?.toExpr()
}

private class Constraint(
  val xs: Map<VarDecl<*>, Rational>,
  val ts: Map<Int, Rational>,
  val constant: Rational,
  val equality: Boolean,
) {
  fun scaled(factor: Rational) =
    Constraint(
      xs.mapValues { it.value * factor },
      ts.mapValues { it.value * factor },
      constant * factor,
      equality,
    )

  operator fun plus(other: Constraint) =
    Constraint(
      add(xs, other.xs),
      add(ts, other.ts),
      constant + other.constant,
      equality && other.equality,
    )

  /** Over the integers: scaled to integer coefficients, then normalized. */
  fun toLiteral(): Literal {
    check(ts.isEmpty())
    val lcm = (xs.values + constant).fold(ONE) { acc, r -> acc / acc.gcd(r.den) * r.den }
    val factor = Rational.of(lcm)
    val terms = xs.map { (v, c) -> v to (c * factor).num }
    return normalizeLinear(terms, equality, -(constant * factor).num)
  }
}

private fun <K> add(a: Map<K, Rational>, b: Map<K, Rational>): Map<K, Rational> =
  (a.keys + b.keys)
    .associateWith { (a[it] ?: Rational.ZERO) + (b[it] ?: Rational.ZERO) }
    .filterValues { it.signum != 0 }

/** Fourier-Motzkin elimination of parameter [k]; an equality on it is solved and substituted. */
private fun eliminate(system: List<Constraint>, k: Int): List<Constraint>? {
  val (involved, without) = system.partition { k in it.ts }
  val definition = involved.firstOrNull { it.equality }
  if (definition != null) {
    val coefficient = definition.ts.getValue(k)
    return without +
      involved
        .filter { it !== definition }
        .map { c ->
          val factor = -(c.ts.getValue(k) / coefficient)
          // c + factor * definition: factor's sign does not matter, definition is an equality
          (c + definition.scaled(factor)).let {
            Constraint(it.xs, it.ts - k, it.constant, c.equality)
          }
        }
  }
  val (upper, lower) = involved.partition { it.ts.getValue(k).signum > 0 }
  val combined =
    upper.flatMap { u ->
      lower.map { l ->
        val sum =
          u.scaled(Rational.ONE / u.ts.getValue(k)) + l.scaled(Rational.ONE / -l.ts.getValue(k))
        Constraint(sum.xs, sum.ts - k, sum.constant, false)
      }
    }
  return without + combined
}

/** The nonzero rows of [rows]' reduced row echelon form. */
private fun rowReduce(rows: List<List<Rational>>): List<List<Rational>> {
  if (rows.isEmpty()) return emptyList()
  val matrix = rows.map { it.toMutableList() }.toMutableList()
  val width = matrix[0].size
  var pivotRow = 0
  for (col in 0 until width) {
    val found = (pivotRow until matrix.size).firstOrNull { matrix[it][col].signum != 0 } ?: continue
    matrix[pivotRow] = matrix[found].also { matrix[found] = matrix[pivotRow] }
    val pivot = matrix[pivotRow][col]
    matrix[pivotRow] = matrix[pivotRow].map { it / pivot }.toMutableList()
    for (r in matrix.indices) {
      if (r == pivotRow || matrix[r][col].signum == 0) continue
      val factor = matrix[r][col]
      matrix[r] =
        matrix[r].indices.map { matrix[r][it] - factor * matrix[pivotRow][it] }.toMutableList()
    }
    pivotRow++
    if (pivotRow == matrix.size) break
  }
  return matrix.take(pivotRow)
}

/** An exact rational with a positive denominator, in lowest terms. */
internal class Rational private constructor(val num: BigInteger, val den: BigInteger) :
  Comparable<Rational> {

  companion object {
    val ZERO = Rational(BigInteger.ZERO, BigInteger.ONE)
    val ONE = Rational(BigInteger.ONE, BigInteger.ONE)

    fun of(num: BigInteger, den: BigInteger = BigInteger.ONE): Rational {
      require(den.signum() != 0)
      val gcd = num.gcd(den)
      val sign = if (den.signum() < 0) BigInteger.ONE.negate() else BigInteger.ONE
      return Rational(num / gcd * sign, den / gcd * sign)
    }
  }

  val signum: Int
    get() = num.signum()

  operator fun plus(other: Rational) = of(num * other.den + other.num * den, den * other.den)

  operator fun minus(other: Rational) = this + -other

  operator fun unaryMinus() = Rational(num.negate(), den)

  operator fun times(other: Rational) = of(num * other.num, den * other.den)

  operator fun div(other: Rational) = of(num * other.den, den * other.num)

  override fun compareTo(other: Rational) = (num * other.den).compareTo(other.num * den)

  override fun equals(other: Any?) = other is Rational && num == other.num && den == other.den

  override fun hashCode() = 31 * num.hashCode() + den.hashCode()

  override fun toString() = if (den == BigInteger.ONE) "$num" else "$num/$den"
}
