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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils

/*
 * Cross-iteration knowledge transfer of the CEGAR loop. Refinement only conjoins constraints, so
 * with π the projection deleting the literal levels added after iteration j, S_k ⊆ π⁻¹(S_j) for
 * k > j. Both sides of the exploration sandwich transfer:
 * - under: a witness cached in iteration j's node decides every later literal syntactically;
 *   extended with those values it is a model of iteration k's node — [seedFromPrevious];
 * - upper: what iteration j knows absent stays absent after lifting — [extractBound] materializes
 *   the explored upper bound as a structural MDD, consumed by
 *   [hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.NegativeNextStateDescriptor].
 */

/** Cross-iteration knowledge of one seeded node kind. */
internal class KindKnowledge {
  /** The previous iteration's node — the witness source of [seedFromPrevious]. */
  var prev: MddHandle? = null
    private set

  /** The accumulated upper bound, consumed by NegativeNextStateDescriptor. */
  var bound: MddHandle? = null
    private set

  /**
   * Folds the iteration's node in. With several split nodes the older knowledge is kept: bounds
   * stay sound (refinement only conjoins), witnesses of one split must not seed another.
   */
  fun update(nodes: List<MddHandle>, dataBoundary: Any?) {
    val node = nodes.singleOrNull() ?: return
    prev = node
    bound = extractBound(node, bound, dataBoundary)
  }
}

/** The accumulated knowledge of the three seeded node kinds. */
internal class SeedKnowledge {
  val trans = KindKnowledge()
  val init = KindKnowledge()
  val prop = KindKnowledge()
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
 * Best-effort transfer of [prev]'s cached witnesses onto [newNodes]: a witness already assigns the
 * levels shared with the previous iteration, so only the new literals are classified — by
 * substitution, without solver calls — and the extended witness is cached as a model of the new
 * node. Witnesses relay: models cached here are part of the new node's caches, so the next
 * iteration's walk of that node sees everything accumulated so far.
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
  val cases = newLiterals.map { binding.bind(it, literalToPred[it]!!) }

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
  cases: List<List<Pair<Decl<*>, Expr<BoolType>>>>,
): Valuation? {
  val extended = MutableValuation.copyOf(witness)
  for (case in cases) {
    for ((decl, expr) in case) {
      val value = ExprUtils.simplify(expr, witness) as? BoolLitExpr ?: return null
      extended.put(decl, Bool(value.value))
    }
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

/**
 * Materializes the explored upper bound of [node] as a structural MDD over the abstract levels,
 * intersected in lockstep with the previous iteration's bound [prev]: cached edges recurse,
 * negatively cached keys are absent, a node the solver exhausted has no default edge (so its keys
 * are exhaustive even on unbounded domains), and unknown regions are permitted by a default edge.
 * Identity and skipped levels constrain nothing at their own level and widen to default edges; the
 * walk is cut at [dataBoundary], the topmost concrete witness level, below which saturation never
 * consults the relation. The lockstep intersection makes the bound accumulate across iterations
 * without composite views or delta set operations, and unknown regions reuse [prev]'s sub-MDDs.
 *
 * The result is level-dense: every level down to the cut carries a node (skipped levels are never
 * emitted), so consumers descend exactly one level per key. Where a default edge is present,
 * explicit edges to terminal zero record keys known absent.
 */
internal fun extractBound(node: MddHandle, prev: MddHandle?, dataBoundary: Any?): MddHandle {
  val extraction = BoundExtraction(node.variableHandle.mddGraph, dataBoundary)
  val result = extraction.walkNode(node, prev)
  return if (result == null) node.variableHandle.mddGraph.terminalZeroHandle
  else node.variableHandle.getHandleFor(result)
}

private class BoundExtraction(graph: MddGraph<*>, private val dataBoundary: Any?) {

  @Suppress("UNCHECKED_CAST")
  private val one: MddNode = (graph as MddGraph<Expr<*>>).getNodeFor(True())
  private val zero: MddNode = graph.terminalZeroNode
  private val zeroHandle: MddHandle = graph.terminalZeroHandle
  private val terminalVariableHandle = graph.terminalVariableHandle

  /** null result = the branch is known absent. */
  private val memo = HashMap<Pair<MddNode, MddNode?>, MddNode?>()

  /** The expression side's knowledge about an edge into the level below. */
  private sealed interface Sub

  /** Known absent. */
  private object Absent : Sub

  /** Unknown, permitted: the bound is the previous bound's remainder. */
  private object Unknown : Sub

  /** The expression tree continues at this handle (positioned at the consuming level). */
  private class At(val handle: MddHandle) : Sub

  /** Virtual level without constraint: every key maps to [sub] one more level down. */
  private class DefaultBelow(val sub: Sub) : Sub

  fun walkNode(e: MddHandle, p: MddHandle?): MddNode? {
    if (p != null && p.isTerminalZero) return null
    if (e.isTerminal) return if (e.isTerminalZero) null else one
    if (atCut(e.variableHandle)) return one
    val pEff = if (p != null && p.isTerminal) null else p

    val key = e.node to pEff?.node
    if (memo.containsKey(key)) return memo[key]

    val varHandle = e.variableHandle
    val result =
      if (e.isSkippedLevel) {
        val lowered = lowerOf(varHandle).getHandleFor(e.node)
        mergeLevel(emptyMap(), At(lowered), pEff, varHandle)
      } else
        when (val repr = e.node.representation) {
          is IdentityRepresentation -> {
            val cont = lowerOf(lowerOf(varHandle)).getHandleFor(repr.continuation)
            mergeLevel(emptyMap(), DefaultBelow(At(cont)), pEff, varHandle)
          }
          is MddExpressionRepresentation -> {
            val explicit = repr.explicitRepresentation
            val lower = lowerOf(varHandle)
            val eMap = LinkedHashMap<Int, Sub>()
            val cached = explicit.cacheView
            val cursor = cached.cursor()
            while (cursor.moveNext()) eMap[cursor.key()] = At(lower.getHandleFor(cursor.value()))
            // a default edge subsumes per-key knowledge
            if (cached.defaultValue() == null) {
              for (k in explicit.negativeKeys) eMap[k] = Absent
            }
            val eDefault =
              cached.defaultValue()?.let { At(lower.getHandleFor(it)) }
                ?: if (explicit.isComplete) Absent else Unknown
            mergeLevel(eMap, eDefault, pEff, varHandle)
          }
          else -> error("Unexpected representation in bound extraction: $repr")
        }
    memo[key] = result
    return result
  }

  /** Builds the bound node at [varHandle] from the expression side's edges and [p]'s. */
  private fun mergeLevel(
    eMap: Map<Int, Sub>,
    eDefault: Sub,
    p: MddHandle?,
    varHandle: MddVariableHandle,
  ): MddNode? {
    val lower = lowerOf(varHandle)
    val aligned = p != null && alignedAt(p, varHandle)

    val keys = LinkedHashSet(eMap.keys)
    if (aligned) {
      val cursor = p!!.node.cursor()
      while (cursor.moveNext()) keys.add(cursor.key())
    }

    val pDefault: MddHandle? =
      when {
        p == null -> null
        !aligned -> p
        else -> pHandleFor(p, p.node.defaultValue())
      }
    val pChildFor: (Int) -> MddHandle? = { key ->
      when {
        p == null -> null
        !aligned -> p
        else -> pHandleFor(p, p.node.get(key) ?: p.node.defaultValue())
      }
    }

    val defaultNode = walkSub(eDefault, pDefault, lower)
    val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    if (defaultNode != null) builder.setDefault(defaultNode)
    var any = false
    for (k in keys) {
      val child = walkSub(eMap[k] ?: eDefault, pChildFor(k), lower)
      if (child != null) {
        builder.set(k, child)
        any = true
      } else if (defaultNode != null) {
        // a key known absent under a permissive default
        builder.set(k, zero)
        any = true
      }
    }
    if (!any && defaultNode == null) return null
    return varHandle.checkInNode(MddStructuralTemplate.of(builder.buildAndReset())).node
  }

  /** The bound below an edge with expression knowledge [sub] and bound remainder [pChild]. */
  private fun walkSub(sub: Sub, pChild: MddHandle?, varHandle: MddVariableHandle): MddNode? {
    if (sub == Absent) return null
    if (pChild != null && pChild.isTerminalZero) return null
    val pEff = if (pChild != null && pChild.isTerminal) null else pChild
    if (atCut(varHandle)) return one
    return when (sub) {
      Unknown -> materialize(pEff, varHandle)
      is At -> walkNode(sub.handle, pEff)
      is DefaultBelow -> mergeLevel(emptyMap(), sub.sub, pEff, varHandle)
      Absent -> error("unreachable")
    }
  }

  /** [p]'s remainder as a node at [varHandle], lifted through unconstrained levels. */
  private fun materialize(p: MddHandle?, varHandle: MddVariableHandle): MddNode {
    if (p == null) return one
    val wraps = mutableListOf<MddVariableHandle>()
    var vh = varHandle
    while (!alignedAt(p, vh)) {
      wraps.add(vh)
      vh = lowerOf(vh)
    }
    var node = p.node
    for (level in wraps.asReversed()) {
      val builder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
      builder.setDefault(node)
      node = level.checkInNode(MddStructuralTemplate.of(builder.buildAndReset())).node
    }
    return node
  }

  /**
   * The child of aligned bound node [p] as a handle. A missing child means absent (the terminal
   * zero handle), never unconstrained: an aligned bound constrains every key.
   */
  private fun pHandleFor(p: MddHandle, child: MddNode?): MddHandle {
    if (child == null || child == zero) return zeroHandle
    return lowerOf(p.variableHandle).getHandleFor(child)
  }

  private fun alignedAt(p: MddHandle, varHandle: MddVariableHandle): Boolean =
    p.variableHandle.variable.map { it.traceInfo }.orElse(null) ==
      varHandle.variable.map { it.traceInfo }.orElse(null)

  private fun atCut(varHandle: MddVariableHandle): Boolean =
    dataBoundary != null && varHandle.variable.map { it.traceInfo }.orElse(null) == dataBoundary

  private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
    if (varHandle.lower.isPresent) varHandle.lower.get() else terminalVariableHandle
}
