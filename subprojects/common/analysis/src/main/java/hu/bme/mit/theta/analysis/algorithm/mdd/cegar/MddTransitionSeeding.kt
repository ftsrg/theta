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

import hu.bme.mit.delta.java.mdd.BinaryOperationCache
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.MddVariableOrder
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityTemplate
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.SolverPool

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
  private val solverPool: SolverPool,
  private val label: String,
  private val logger: Logger,
) {
  /** The previous iteration's node — the witness source of [seedFromPrevious]. */
  var prev: MddHandle? = null
    private set

  /** The previous iteration's upper bound: its visited-edge snapshot, lifted and AND-ed on consumption. */
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
    seedFromPrevious(prev, newNodes, newLiterals, literalToPred, binding, solverPool, logger, label)
  }

  /**
   * Folds the iteration's nodes in. With several split nodes the older knowledge is kept: bounds
   * stay sound (refinement only conjoins), witnesses of one split must not seed another.
   */
  fun update() {
    val node = nodes.singleOrNull() ?: return
    prev = node
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
  solverPool: SolverPool,
  logger: Logger,
) {
  val trans =
    CrossIterationKnowledge(
      transBinding, transDataBoundary, transBoundOrder, solverPool, "Transition", logger)
  val init =
    CrossIterationKnowledge(
      stateBinding, stateDataBoundary, stateBoundOrder, solverPool, "Init", logger)
  val prop =
    CrossIterationKnowledge(
      stateBinding, stateDataBoundary, stateBoundOrder, solverPool, "Property", logger)
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
 * Seeds [newNodes] from [prev]'s known transitions without flattening them to a set of witnesses. The
 * previous relation is extracted solver-free into a fresh mirror graph and restricted case by case —
 * one case per new-literal binding, as if each literal had arrived in its own iteration: the two
 * predicate cofactors of a case become the edges of a new level checked in on top of the running
 * mirror MDD, so an empty cofactor prunes every literal combination below it and shared cofactor
 * results are built once. The finished mirror carries the new-literal levels as ordinary edges and one
 * [MddExpressionRepresentation.cacheModel] walk relays it. The cofactor constraints are decided purely
 * by substitution, so seeding stays solver-free; identity levels of the relation survive a case that
 * is silent on them and drop the subtree otherwise (see [SeedRestrictor]).
 */
internal fun seedFromPrevious(
  prev: MddHandle?,
  newNodes: List<MddHandle>,
  newLiterals: List<VarDecl<BoolType>>,
  literalToPred: Map<Decl<*>, Expr<BoolType>>,
  binding: LiteralBinding,
  solverPool: SolverPool,
  logger: Logger,
  label: String,
) {
  // single node assumed: with several split nodes, a transition of one split could be cached into
  // another split's node, corrupting it
  if (prev == null || newLiterals.isEmpty() || newNodes.size != 1) return
  val newTop = expressionTop(newNodes[0]) ?: return
  // the new node's top-down literal layout: newest literal highest, the unprimed level of a pair
  // above the primed one — the mirror below must repeat it level by level, cacheModel walks lockstep
  val cases = newLiterals.asReversed().flatMap { binding.bind(it, literalToPred[it]!!) }

  val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(prev.variableHandle)
  val known = MddExplicitRepresentationExtractor.transform(prev, mirrorTop)

  val cofactors =
    cases.map { (_, pred) ->
      listOf(pred, Not(pred)).map {
        mirrorTop
          .checkInNode(
            MddExpressionTemplate.ofSubstitution(it, { d -> d as Decl<*> }, solverPool, true)
          )
          .node
      }
    }
  // case levels on top of the mirror, created bottom-up; domain 3 so a template with both truth
  // values and equal children can never count as domain-covering and canonize the level away
  val mirrorOrder = mirrorTop.variable.get().mddVariableOrder
  cases.asReversed().forEach { (decl, _) ->
    mirrorOrder.createOnTop(MddVariableDescriptor.create(decl, 3))
  }
  val caseTops = ArrayList<MddVariableHandle>(cases.size)
  run {
    var top = mirrorOrder.defaultSetSignature.topVariableHandle
    repeat(cases.size) {
      caseTops.add(top)
      top = top.lower.get()
    }
  }

  val restrictor = SeedRestrictor(mirrorTop.mddGraph)
  val memo = HashMap<Pair<Int, MddNode>, MddNode>()
  var leaves = 0L
  fun build(caseIdx: Int, current: MddNode): MddNode {
    if (current === restrictor.zero) return current
    if (caseIdx == cases.size) {
      leaves++
      return current
    }
    memo[caseIdx to current]?.let {
      return it
    }
    val (pos, neg) = cofactors[caseIdx]
    val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    build(caseIdx + 1, restrictor.restrict(current, pos, mirrorTop)).let {
      if (it !== restrictor.zero) templateBuilder.set(1, it)
    }
    build(caseIdx + 1, restrictor.restrict(current, neg, mirrorTop)).let {
      if (it !== restrictor.zero) templateBuilder.set(0, it)
    }
    val result =
      caseTops[caseIdx].checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset())).node
    memo[caseIdx to current] = result
    return result
  }

  val union = build(0, known.node)
  if (union !== restrictor.zero) newTop.cacheModel(ImmutableValuation.builder().build(), union)

  logger.write(
    Logger.Level.MAINSTEP,
    "%s seeding: newLiterals=%d, cases=%d, seededLeaves=%d\n",
    label,
    newLiterals.size,
    cases.size,
    leaves,
  )
}

/**
 * `known ∩ constraint` over the mirror graph, like delta's intersection — the explicit side drives,
 * the substitution-only constraint is probed by key, and a known default survives only a constraint
 * level with no structure — but identity-aware, which the generic operation is not (an
 * [IdentityRepresentation] has a null cursor): a pair the constraint is silent on stays identity, a
 * constrained pair drops the subtree, as those transitions are not decidable by substitution.
 */
private class SeedRestrictor(private val graph: MddGraph<*>) {
  val zero: MddNode = graph.terminalZeroNode
  private val cache = BinaryOperationCache<MddNode, MddNode, MddNode>()

  fun restrict(known: MddNode, constraint: MddNode, variable: MddVariableHandle): MddNode {
    if (known === zero || constraint === zero) return zero
    if (!variable.variable.isPresent) return graph.intersectionTerminal(known, constraint)
    cache.getOrNull(known, constraint)?.let {
      return it
    }
    val result = compute(known, constraint, variable)
    cache.addToCache(known, constraint, result)
    return result
  }

  private fun compute(known: MddNode, constraint: MddNode, variable: MddVariableHandle): MddNode {
    val repr = known.representation
    if (repr is IdentityRepresentation) {
      val primed = lowerOf(variable)
      val cBelow = silentChild(constraint, variable) ?: return zero
      val cBelowPair = silentChild(cBelow, primed) ?: return zero
      val continuation = restrict(repr.continuation, cBelowPair, lowerOf(primed))
      return if (continuation === zero) zero
      else variable.checkInNode(IdentityTemplate(continuation)).node
    }
    val cSilent = silentChild(constraint, variable)
    val lower = lowerOf(variable)
    val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    val onLevel = known.isOn(variable.variable.get())
    if (onLevel) {
      val cursor = known.cursor()
      while (cursor.moveNext()) {
        val cChild = cSilent ?: constraint.get(cursor.key()) ?: continue
        val restricted = restrict(cursor.value(), cChild, lower)
        if (restricted !== zero) templateBuilder.set(cursor.key(), restricted)
      }
    }
    val kDefault = if (onLevel) known.defaultValue() else known
    // a default against a constrained level is dropped: neither side can enumerate the other
    if (kDefault != null && cSilent != null) {
      val restricted = restrict(kDefault, cSilent, lower)
      if (restricted !== zero) templateBuilder.setDefault(restricted)
    }
    return variable.checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset())).node
  }

  /** The constraint's continuation below [variable] if it has no structure there, else null. */
  private fun silentChild(constraint: MddNode, variable: MddVariableHandle): MddNode? =
    if (constraint.isOn(variable.variable.get())) constraint.defaultValue() else constraint
}

private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
  if (varHandle.lower.isPresent) varHandle.lower.get() else varHandle.mddGraph.terminalVariableHandle

/** The expression node at the top of [handle], unwrapping identity levels. */
private fun expressionTop(handle: MddHandle): MddExpressionRepresentation? {
  var node = handle.node
  while (!node.isTerminal && node.representation is IdentityRepresentation) {
    node = (node.representation as IdentityRepresentation).continuation
  }
  return if (node.isTerminal) null else node.representation as? MddExpressionRepresentation
}

