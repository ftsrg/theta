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
package hu.bme.mit.theta.analysis.algorithm.mdd.cegar

import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddVariableOrder
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils

/*
 * Cross-iteration knowledge transfer of the CEGAR loop. Refinement only conjoins constraints, so the
 * previous iteration's knowledge carries to the next on both sides of the exploration sandwich:
 * - under: a witness cached in the previous node decides every later literal by substitution, so
 *   extended it is a model of the next node — [seedFromPrevious];
 * - upper: what the previous iteration confirmed present over-approximates the next once lifted —
 *   [update] extracts it as a structural bound (MddExplicitRepresentationExtractor), consumed as an
 *   AndNextStateDescriptor operand (the relation and init/prop bound) and by `filterStates` for the
 *   property. Only the last iteration is read: its constrained exploration already excludes everything
 *   earlier iterations pruned, so the bound needs no accumulation.
 */

/** Cross-iteration knowledge of one seeded node kind. */
internal class CrossIterationKnowledge(
  private val binding: LiteralBinding,
  private val dataBoundary: Any?,
  private val boundOrder: MddVariableOrder?,
  private val label: String,
  private val logger: Logger,
) {
  /** The previous iteration's node — the witness source of [seedFromPrevious]. */
  var prev: MddHandle? = null
    private set

  /** The previous iteration's upper bound: its SAT cache snapshot, lifted and AND-ed on consumption. */
  var bound: MddHandle? = null
    private set

  private var nodes: List<MddHandle> = emptyList()

  /** Relays the previous iteration's witnesses onto [newNodes] and remembers them for [update]. */
  fun seed(
    newNodes: List<MddHandle>,
    newLiterals: List<VarDecl<BoolType>>,
    literalToPred: Map<Decl<*>, Expr<BoolType>>,
  ) {
    nodes = newNodes
    seedFromPrevious(prev, newNodes, newLiterals, literalToPred, binding, logger, label)
  }

  /**
   * Folds the iteration's nodes in. With several split nodes the older knowledge is kept: bounds
   * stay sound (refinement only conjoins), witnesses of one split must not seed another.
   */
  fun update() {
    val node = nodes.singleOrNull() ?: return
    prev = node
    // the upper bound: the node's present-cache structure, extracted over the abstract levels and
    // truncated at the concrete witness boundary. The present cache is exhaustive — an unprobed key is
    // unsatisfiable, since GSAT probes every transition of every reachable source
    bound =
      boundOrder?.let {
        MddExplicitRepresentationExtractor.transform(
          node,
          it.defaultSetSignature.topVariableHandle,
          dataBoundary,
        )
      }
  }
}

/** The accumulated knowledge of the three seeded node kinds. */
internal class SeedKnowledge(
  transBinding: LiteralBinding,
  transDataBoundary: Any?,
  stateDataBoundary: Any?,
  transBoundOrder: MddVariableOrder?,
  stateBoundOrder: MddVariableOrder?,
  logger: Logger,
) {
  val trans = CrossIterationKnowledge(transBinding, transDataBoundary, transBoundOrder, "Transition", logger)
  val init = CrossIterationKnowledge(stateBinding, stateDataBoundary, stateBoundOrder, "Init", logger)
  val prop = CrossIterationKnowledge(stateBinding, stateDataBoundary, stateBoundOrder, "Property", logger)
}

/** Binds a literal's defining predicate to the decls of the levels the literal occupies. */
internal fun interface LiteralBinding {
  fun bind(literal: VarDecl<BoolType>, pred: Expr<BoolType>): List<Pair<Decl<*>, Expr<BoolType>>>
}

/** Transition nodes: a literal binds at both its unprimed and its primed level. */
internal fun transitionBinding(concreteModel: MonolithicExpr) = LiteralBinding { literal, pred ->
  listOf(
    literal.getConstDecl(0) to PathUtils.unfold(pred, 0),
    literal.getConstDecl(1) to
      PathUtils.unfold(ExprUtils.applyPrimes(pred, concreteModel.transOffsetIndex), 0),
  )
}

/** State (init, property) nodes: a literal binds at its unprimed level only. */
internal val stateBinding = LiteralBinding { literal, pred ->
  listOf(literal.getConstDecl(0) to PathUtils.unfold(pred, 0))
}

/**
 * Transfers [prev]'s cached witnesses onto [newNodes]: a witness already assigns the shared levels,
 * so only the new literals are classified — by substitution, no solver calls — and the extended
 * witness is cached as a model of the new node, relaying it to later iterations' walks.
 */
internal fun seedFromPrevious(
  prev: MddHandle?,
  newNodes: List<MddHandle>,
  newLiterals: List<VarDecl<BoolType>>,
  literalToPred: Map<Decl<*>, Expr<BoolType>>,
  binding: LiteralBinding,
  logger: Logger,
  label: String,
) {
  // single node assumed: with several split nodes, a witness of one split could be cached into
  // another split's node, corrupting it
  if (prev == null || newLiterals.isEmpty() || newNodes.size != 1) return
  val newTop = expressionTop(newNodes[0]) ?: return
  val cases = newLiterals.flatMap { binding.bind(it, literalToPred[it]!!) }

  var seeded = 0L
  // witnesses that do not assign all predicate variables (identity and default levels carry no
  // assignment), leaving a predicate undecided
  var unresolved = 0L
  for (witness in MddKnownValuationCollector.collect(prev)) {
    val classified = classify(witness, cases)
    if (classified == null) {
      unresolved++
    } else {
      newTop.cacheModel(classified)
      seeded++
    }
  }

  logger.write(
    Logger.Level.MAINSTEP,
    "%s seeding: newLiterals=%d, seeded=%d, unresolved=%d\n",
    label,
    newLiterals.size,
    seeded,
    unresolved,
  )
}

/** Extends [witness] with the truth value of every literal case; null if any is undecided. */
private fun classify(
  witness: Valuation,
  cases: List<Pair<Decl<*>, Expr<BoolType>>>,
): Valuation? {
  val extended = MutableValuation.copyOf(witness)
  for ((decl, expr) in cases) {
    val value = ExprUtils.simplify(expr, witness) as? BoolLitExpr ?: return null
    extended.put(decl, Bool(value.value))
  }
  return extended
}

/** The expression node at the top of [handle], unwrapping identity levels. */
private fun expressionTop(handle: MddHandle): MddExpressionRepresentation? {
  var node = handle.node
  while (!node.isTerminal && node.representation is IdentityRepresentation) {
    node = (node.representation as IdentityRepresentation).continuation
  }
  return if (node.isTerminal) null else node.representation as? MddExpressionRepresentation
}

