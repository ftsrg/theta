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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or

/** The generalization methods of `--dss-generalizers` and `--dss-conjecture-generalizers`. */
enum class DssGeneralizerKind {
  /** Conjectures over the drift of each sender's conditions ([ViolationGeneralizer]). */
  GSPACER,
  /** Drops literals while the rest stays unreachable ([SemanticGeneralizer]). */
  SEMANTIC,
}

/** The default bound on the back edges a path takes in `SEMANTIC`'s check in a cyclic block. */
const val DEFAULT_SEMANTIC_UNROLLINGS = 3

/** How the generalizers of one list make a single generalization. */
enum class DssGeneralizerCombination {
  /** The first generalizer with a candidate, in list order. */
  FIRST,
  /** The disjunction of every candidate. */
  UNION,
  /** Each generalizer weakens the previous result, starting from the received conditions. */
  CHAIN,
}

/**
 * What a generalizer may ask: [isUnsat] (an undecided query must throw), and [unreachable], null
 * where unreachability cannot be checked.
 */
class GeneralizationContext(
  val isUnsat: (Expr<BoolType>) -> Boolean,
  val unreachable: ((Expr<BoolType>) -> Boolean)? = null,
)

/** A may condition covering received conditions, and the candidates of each method it came from. */
class Generalization
internal constructor(val condition: Expr<BoolType>, internal val parts: List<Part>) {

  internal class Part(val kind: DssGeneralizerKind, val condition: Expr<BoolType>, val token: Any)

  val kinds: List<DssGeneralizerKind>
    get() = parts.map { it.kind }
}

/**
 * The generalizers of [kinds], in order, combined by [combination]. Every result is weaker than the
 * received conditions, and none is valid.
 */
class Generalizers(
  kinds: List<DssGeneralizerKind>,
  private val combination: DssGeneralizerCombination,
  gas: Int,
) {

  private val order = kinds.distinct()
  private val gspacer = if (DssGeneralizerKind.GSPACER in order) ViolationGeneralizer(gas) else null
  private val semantic =
    if (DssGeneralizerKind.SEMANTIC in order) SemanticGeneralizer(gas) else null

  init {
    require(order.isNotEmpty()) { "No generalizer to combine" }
  }

  fun record(sender: String, condition: Expr<BoolType>) {
    gspacer?.record(sender, condition)
  }

  fun generalize(
    received: List<Pair<String, Expr<BoolType>>>,
    context: GeneralizationContext,
  ): Generalization? {
    if (received.isEmpty()) return null
    val exact = Or(received.map { it.second })
    val key = received.map { it.first }.distinct().sorted().joinToString(",")
    val parts = mutableListOf<Generalization.Part>()
    var current = exact
    for (kind in order) {
      val part =
        when (kind) {
          DssGeneralizerKind.GSPACER ->
            gspacer!!.generalize(received, context.isUnsat)?.let {
              Generalization.Part(kind, it.condition, it)
            }
          DssGeneralizerKind.SEMANTIC -> {
            val base = if (combination == DssGeneralizerCombination.CHAIN) current else exact
            semantic!!.generalize(key, base, context)?.let {
              Generalization.Part(kind, it.condition, it)
            }
          }
        } ?: continue
      parts += part
      when (combination) {
        DssGeneralizerCombination.FIRST -> break
        DssGeneralizerCombination.UNION -> {}
        DssGeneralizerCombination.CHAIN ->
          current =
            if (kind == DssGeneralizerKind.GSPACER) Or(current, part.condition) else part.condition
      }
    }
    if (parts.isEmpty()) return null
    val condition =
      when (combination) {
        DssGeneralizerCombination.FIRST -> parts.single().condition
        DssGeneralizerCombination.UNION -> Or(parts.map { it.condition })
        DssGeneralizerCombination.CHAIN -> current
      }
    val canonical = DssAuxVars.canonicalize(condition)
    if (context.isUnsat(Not(canonical)) || context.isUnsat(And(canonical, Not(exact)))) return null
    return Generalization(canonical, parts)
  }

  /** [generalization] was reached: each method it came from learns that of its candidate. */
  fun failed(generalization: Generalization) {
    for (part in generalization.parts) {
      when (part.kind) {
        DssGeneralizerKind.GSPACER ->
          gspacer!!.failed(part.token as ViolationGeneralizer.Generalization)
        DssGeneralizerKind.SEMANTIC ->
          semantic!!.failed(part.token as SemanticGeneralizer.Candidate)
      }
    }
  }
}

/**
 * Semantic generalization: each cube of a condition loses literals one at a time while the rest
 * stays [GeneralizationContext.unreachable]; for `x == -2 && n >= -1` and states with `x >= 0` this
 * gives `x <= -2`. Each sender has [gas] failed candidates.
 */
class SemanticGeneralizer(private val gas: Int) {

  init {
    require(gas > 0)
  }

  class Candidate internal constructor(val condition: Expr<BoolType>, internal val key: String)

  private val gasLeft = HashMap<String, Int>()
  private val failedCandidates = HashSet<Expr<BoolType>>()

  /** A strictly weaker, still unreachable condition than [condition], or null. */
  fun generalize(
    key: String,
    condition: Expr<BoolType>,
    context: GeneralizationContext,
  ): Candidate? {
    if ((gasLeft[key] ?: gas) <= 0) return null
    val unreachable = context.unreachable ?: return null
    val cubes = normalizedCubes(condition)?.takeIf { it.isNotEmpty() } ?: return null
    // A reachable condition cannot have an unreachable weakening: the exact analysis decides
    if (!unreachable(condition)) return null
    val result = DssAuxVars.canonicalize(Or(cubes.map { weaken(it, unreachable) }))
    if (result in failedCandidates) return null
    if (context.isUnsat(Not(result)) || context.isUnsat(And(result, Not(condition)))) return null
    return Candidate(result, key)
  }

  fun failed(candidate: Candidate) {
    gasLeft.merge(candidate.key, gas - 1) { left, _ -> left - 1 }
    failedCandidates += candidate.condition
  }

  private fun weaken(cube: Cube, unreachable: (Expr<BoolType>) -> Boolean): Expr<BoolType> {
    val literals = (cube.linear.flatMap(::bounds).map { it.toExpr() } + cube.opaque).toMutableList()
    var index = 0
    while (index < literals.size) {
      val rest = literals.filterIndexed { other, _ -> other != index }
      val droppable =
        DssAuxVars.collectVars(literals[index]).isEmpty() &&
          rest.isNotEmpty() &&
          unreachable(And(rest))
      if (droppable) literals.removeAt(index) else index++
    }
    return And(literals)
  }

  private fun bounds(literal: LinearLiteral): List<LinearLiteral> =
    if (!literal.equality) listOf(literal)
    else
      listOf(
        LinearLiteral(literal.terms, false, literal.bound),
        LinearLiteral(
          literal.terms.map { (v, c) -> v to c.negate() },
          false,
          literal.bound.negate(),
        ),
      )
}
