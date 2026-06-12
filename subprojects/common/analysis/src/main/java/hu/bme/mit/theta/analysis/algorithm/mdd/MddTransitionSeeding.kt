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

import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils

/**
 * Best-effort transfer of the previous iteration's transition relation onto the new literals. The
 * previous relation stores, below the abstract levels, the concrete (source, target) witnesses that
 * the solver produced during exploration. Each witness is a full assignment, so substituting it
 * into the new predicates reduces them to literals: this decides syntactically, without solver
 * calls, which combination of new-literal values (the T/T, T/F, F/T, F/F cases) the witness
 * belongs to. The witness extended with those values is a model of the new relation and is cached
 * into its expression node.
 */
internal fun seedTransitions(
  prevTransNodes: List<MddHandle>,
  newTransNodes: List<MddHandle>,
  newLiterals: List<VarDecl<BoolType>>,
  literalToPred: Map<Decl<*>, Expr<BoolType>>,
  concreteModel: MonolithicExpr,
  logger: Logger,
) =
  seedExpressionNode(prevTransNodes, newTransNodes, newLiterals, logger, "Transition") { literal ->
    val pred = literalToPred[literal]!!
    listOf(
      literal.getConstDecl(0) to PathUtils.unfold(pred, 0),
      literal.getConstDecl(1) to
        PathUtils.unfold(ExprUtils.applyPrimes(pred, concreteModel.transOffsetIndex), 0),
    )
  }

/** [seedTransitions] for state expressions (init, property): one unprimed level per literal. */
internal fun seedStateNode(
  prevNode: MddHandle?,
  newNode: MddHandle,
  newLiterals: List<VarDecl<BoolType>>,
  literalToPred: Map<Decl<*>, Expr<BoolType>>,
  logger: Logger,
  label: String,
) =
  seedExpressionNode(listOfNotNull(prevNode), listOf(newNode), newLiterals, logger, label) {
    literal ->
    listOf(literal.getConstDecl(0) to PathUtils.unfold(literalToPred[literal]!!, 0))
  }

private fun seedExpressionNode(
  prevNodes: List<MddHandle>,
  newNodes: List<MddHandle>,
  newLiterals: List<VarDecl<BoolType>>,
  logger: Logger,
  label: String,
  literalCases: (VarDecl<BoolType>) -> List<Pair<Decl<*>, Expr<BoolType>>>,
) {
  // single node assumed: with several split nodes, a witness of one split could be
  // cached into another split's node, corrupting it
  if (newLiterals.isEmpty() || newNodes.size != 1 || prevNodes.isEmpty()) return

  var node = newNodes[0].node
  while (!node.isTerminal && node.representation is IdentityRepresentation) {
    node = (node.representation as IdentityRepresentation).continuation
  }
  if (node.isTerminal) return
  val newTop = node.representation as? MddExpressionRepresentation ?: return

  val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(prevNodes[0].variableHandle)
  val struct =
    prevNodes
      .map { MddExplicitRepresentationExtractor.transform(it, mirrorTop) }
      .reduce { a, b -> a.union(b) as MddHandle }

  val cases = newLiterals.map(literalCases)

  var seeded = 0L
  // witnesses that do not assign all predicate variables (identity and default levels carry no
  // assignment), leaving a predicate undecided
  var unresolved = 0L
  val assignments = ArrayDeque<Pair<Decl<*>, LitExpr<*>>>()

  fun emit() {
    val builder = ImmutableValuation.builder()
    assignments.forEach { (decl, value) -> builder.put(decl, value) }
    val witness = builder.build()
    for (case in cases) {
      for ((decl, expr) in case) {
        val value = ExprUtils.simplify(expr, witness) as? BoolLitExpr
        if (value == null) {
          unresolved++
          return
        }
        builder.put(decl, Bool(value.value))
      }
    }
    newTop.cacheModel(builder.build())
    seeded++
  }

  fun collect(handle: MddHandle) {
    if (handle.isTerminal) {
      if (!handle.isTerminalZero) emit()
      return
    }
    val repr = handle.node.representation
    if (repr is IdentityRepresentation) {
      collect(
        handle.variableHandle.lower.orElseThrow().lower.orElseThrow().getHandleFor(
          repr.continuation
        )
      )
      return
    }
    if (!handle.defaultValue().isTerminalZero) {
      collect(handle.defaultValue())
      return
    }
    val decl = handle.variableHandle.variable.orElseThrow().getTraceInfo(Decl::class.java)
    val cursor = handle.cursor()
    while (cursor.moveNext()) {
      assignments.addLast(decl to LitExprConverter.toLitExpr(cursor.key(), decl.type))
      collect(cursor.value() as MddHandle)
      assignments.removeLast()
    }
  }

  collect(struct)

  logger.write(
    Logger.Level.MAINSTEP,
    "%s seeding: newLiterals=%d, seeded=%d, unresolved=%d\n",
    label,
    newLiterals.size,
    seeded,
    unresolved,
  )
}
