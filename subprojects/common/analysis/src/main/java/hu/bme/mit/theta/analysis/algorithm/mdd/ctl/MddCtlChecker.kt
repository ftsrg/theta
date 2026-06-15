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
package hu.bme.mit.theta.analysis.algorithm.mdd.ctl

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeInitializer
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.RelationDrivenAndNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.ReverseNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SingleStepProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.StateSpaceEnumerationProvider
import hu.bme.mit.theta.common.collection.CollectionUtil
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool

/**
 * Symbolic CTL model checker over the MDD/saturation backend, based on Zhao & Ciardo, *Symbolic CTL
 * Model Checking of Asynchronous Systems Using Constrained Saturation* (ATVA 2009). EX, EU and EG
 * are the primitives; the remaining operators are rewritten to these. Formulas are evaluated over
 * the reachable state space, and negation is complement against it.
 */
class MddCtlChecker
@JvmOverloads
constructor(
  private val monolithicExpr: MonolithicExpr,
  private val solverPool: SolverPool,
  private val logger: Logger,
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  private val variableOrdering: List<VarDecl<*>> = monolithicExpr.orderVars(),
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL,
  private val euStrategy: EuStrategy = EuStrategy.CONSTRAINED_SATURATION,
) {

  /** How `E[phi U psi]` is computed. */
  enum class EuStrategy {
    /** A single constrained backward saturation call. */
    CONSTRAINED_SATURATION,
    /** The lfp loop `mu Z. psi | (phi & pre(Z))` over single backward steps. */
    FIXPOINT_LOOP,
  }

  private val stateSig: MddSignature
  private val transSig: MddSignature
  private val topVar: MddVariableHandle

  /** The reachable state space. */
  val stateSpace: MddHandle
  val initNode: MddHandle

  private val reversedNS: AbstractNextStateDescriptor

  private val stateSpaceProvider: StateSpaceEnumerationProvider
  private val singleStepProvider: SingleStepProvider

  private val memo = HashMap<CtlExpr, MddHandle>()

  private val universe: MddHandle
    get() = stateSpace

  init {
    val mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
    val mddGraph2 = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
    mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    mddGraph2.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)

    val stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph)
    val transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph2)

    variableOrdering.forEach {
      Preconditions.checkArgument(
        monolithicExpr.vars.contains(it),
        "Variable ordering contains variable not present in vars List",
      )
    }
    Preconditions.checkArgument(
      variableOrdering.size == CollectionUtil.createSet(variableOrdering).size,
      "Variable ordering contains duplicates",
    )

    val identityExprs = mutableListOf<Expr<BoolType>>()
    for (v in variableOrdering.reversed()) {
      val domainSize = 0

      stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))

      val index = monolithicExpr.transOffsetIndex[v]
      if (index > 0) {
        transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(index), domainSize))
      } else {
        transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), domainSize))
        identityExprs.add(Eq(v.getConstDecl(0).ref, v.getConstDecl(1).ref))
      }
      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))
    }

    stateSig = stateOrder.defaultSetSignature
    transSig = transOrder.defaultSetSignature
    topVar = stateSig.topVariableHandle

    val initExpr = PathUtils.unfold(monolithicExpr.initExpr, 0)
    initNode = topVar.checkInNode(MddExpressionTemplate.of(initExpr, { it as Decl<*> }, solverPool))
    logger.write(Logger.Level.INFO, "Created initial node\n")

    val transNodes = mutableListOf<MddHandle>()
    val descriptors = mutableListOf<AbstractNextStateDescriptor>()
    for (expr in monolithicExpr.split) {
      val transExpr =
        And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(identityExprs))
      val transitionNode =
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.of(transExpr, { it as Decl<*> }, solverPool, true)
        )
      transNodes.add(transitionNode)
      descriptors.add(MddNodeNextStateDescriptor.of(transitionNode))
    }
    val nextStates: AbstractNextStateDescriptor = OrNextStateDescriptor.create(descriptors)

    stateSpaceProvider = iterationStrategy.createProvider(stateSig.variableOrder)
    stateSpace = stateSpaceProvider.compute(MddNodeInitializer.of(initNode), nextStates, topVar)
    logger.write(
      Logger.Level.INFO,
      "Calculated state space, size: ${MddInterpreter.calculateNonzeroCount(stateSpace)}\n",
    )

    val reversedDescriptors = mutableListOf<AbstractNextStateDescriptor>()
    val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(transSig.topVariableHandle)
    for (transNode in transNodes) {
      val explTrans = MddExplicitRepresentationExtractor.transform(transNode, mirrorTop)
      reversedDescriptors.add(ReverseNextStateDescriptor.of(stateSpace, explTrans))
    }
    reversedNS = OrNextStateDescriptor.create(reversedDescriptors)

    singleStepProvider = SingleStepProvider(stateSig.variableOrder)
  }

  /** Evaluates [expr] to the set of (reachable) states satisfying it. */
  fun check(expr: CtlExpr): MddHandle = eval(expr)

  /** True iff every initial state satisfies [expr]. */
  fun isSatisfied(expr: CtlExpr): Boolean {
    // the symbolic initNode cannot drive set operations, so instead of subtracting from it, it is
    // intersected with the explicit complement (which queries it key-by-key only)
    val violating = eval(CtlExpr.Not(expr)).intersection(initNode)
    return MddInterpreter.calculateNonzeroCount(violating) == 0L
  }

  /** States with at least one successor in [x]. */
  private fun pre(x: MddHandle): MddHandle =
    singleStepProvider.compute(MddNodeInitializer.of(x), reversedNS, topVar)

  /**
   * `E[phi U psi]` as a single constrained backward fixed-point call. The constraint is phi | psi
   * (not phi alone) so that seed states outside phi are not pruned.
   */
  private fun euSaturation(p: MddHandle, q: MddHandle): MddHandle {
    val constraint = p.union(q)
    val saturated =
      stateSpaceProvider.compute(
        MddNodeInitializer.of(q),
        RelationDrivenAndNextStateDescriptor.of(reversedNS, constraint),
        topVar,
      )
    return saturated.intersection(universe)
  }

  /** `E[phi U psi]` by the lfp loop `mu Z. psi | (phi & pre(Z))`. */
  private fun euFixpointLoop(p: MddHandle, q: MddHandle): MddHandle {
    var z = q
    while (true) {
      val next = q.union(p.intersection(pre(z)))
      if (next.node === z.node) break
      z = next
    }
    return z
  }

  private fun eval(phi: CtlExpr): MddHandle =
    memo.getOrPut(phi) {
      when (phi) {
        is CtlExpr.Atom -> {
          val node =
            topVar.checkInNode(
              MddExpressionTemplate.of(PathUtils.unfold(phi.expr, 0), { it as Decl<*> }, solverPool)
            )
          // the explicit universe must drive the intersection: the symbolic atom node has an
          // unbounded keyset and can only be queried key-by-key
          universe.intersection(node)
        }

        is CtlExpr.Top -> universe

        is CtlExpr.Not -> universe.minus(eval(phi.op))
        is CtlExpr.And -> eval(phi.l).intersection(eval(phi.r))
        is CtlExpr.Or -> eval(phi.l).union(eval(phi.r))

        is CtlExpr.EX -> pre(eval(phi.op))

        is CtlExpr.EU -> {
          val p = eval(phi.l)
          val q = eval(phi.r)
          when (euStrategy) {
            EuStrategy.CONSTRAINED_SATURATION -> euSaturation(p, q)
            EuStrategy.FIXPOINT_LOOP -> euFixpointLoop(p, q)
          }
        }

        // EG phi = nu Z. phi & pre(Z); saturation cannot compute greatest fixed points
        is CtlExpr.EG -> {
          var x = eval(phi.op)
          while (true) {
            val next = x.intersection(pre(x))
            if (next.node === x.node) break
            x = next
          }
          x
        }

        is CtlExpr.EF -> eval(CtlExpr.EU(CtlExpr.Top, phi.op))
        is CtlExpr.AX -> eval(CtlExpr.Not(CtlExpr.EX(CtlExpr.Not(phi.op))))
        is CtlExpr.AG -> eval(CtlExpr.Not(CtlExpr.EF(CtlExpr.Not(phi.op))))
        is CtlExpr.AF -> eval(CtlExpr.Not(CtlExpr.EG(CtlExpr.Not(phi.op))))
        is CtlExpr.AU ->
          eval(
            CtlExpr.Not(
              CtlExpr.Or(
                CtlExpr.EU(CtlExpr.Not(phi.r), CtlExpr.And(CtlExpr.Not(phi.l), CtlExpr.Not(phi.r))),
                CtlExpr.EG(CtlExpr.Not(phi.r)),
              )
            )
          )
      }
    }
}
