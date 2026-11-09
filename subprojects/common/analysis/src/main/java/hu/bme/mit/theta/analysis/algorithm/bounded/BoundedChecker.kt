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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import java.util.*
import java.util.concurrent.atomic.AtomicInteger

/**
 * A checker for bounded model checking.
 *
 * @param <S> The state type, must inherit from ExprState.
 * @param <A> The action type, must inherit from StmtAction.
 * @param monolithicExpr The monolithic expression to be checked
 * @param shouldGiveUp A function determining whether to give up checking based on a given iteration
 *   count. Use this to implement custom timeout or thread interruption checking subroutines.
 * @param bmcSolver The solver for bounded model checking.
 * @param bmcEnabled A function determining whether bounded model checking is enabled. Cannot be
 *   disabled per-iteration. Use the capabilities of the lambda parameter to decide on enabledness
 *   based on external factors, such as available memory or time limit remaining.
 * @param lfPathOnly A function determining whether to consider only loop-free paths.
 * @param itpSolver The solver for interpolation, used in IMC.
 * @param imcEnabled A function determining whether IMC is enabled. Can be different per-iteration.
 * @param indSolver The solver for induction checking in KIND.
 * @param kindEnabled A function determining whether k-induction (KIND) is enabled.
 * @param logger The logger for logging.
 * @param needProof Whether a safe result carries an invariant, over-approximating the reachable
 *   states; otherwise its proof is `true`.
 * @param interpolateProof Whether that invariant is projected onto the model's variables by
 *   interpolation (with [itpSolver]), which need not keep it inductive; without it, or if that
 *   fails, the other states of its paths are free variables, i.e. implicitly existential.
 */
class BoundedChecker
@JvmOverloads
constructor(
  private val monolithicExpr: MonolithicExpr,
  private val shouldGiveUp: (Int) -> Boolean = { false },
  private val bmcSolver: Solver? = null,
  private val bmcEnabled: () -> Boolean = { bmcSolver != null },
  private val lfPathOnly: () -> Boolean = { true },
  private val itpSolver: ItpSolver? = null,
  private val imcEnabled: (Int) -> Boolean = { itpSolver != null },
  private val indSolver: Solver? = null,
  private val kindEnabled: (Int) -> Boolean = { indSolver != null },
  private val logger: Logger,
  private val needProof: Boolean = false,
  private val interpolateProof: Boolean = false,
) : SafetyChecker<PredState, Trace<ExplState, ExprAction>, UnitPrec> {

  private val vars = monolithicExpr.vars
  private val unfoldedInitExpr =
    PathUtils.unfold(monolithicExpr.initExpr, VarIndexingFactory.indexing(0))
  private val unfoldedPropExpr = { i: VarIndexing -> PathUtils.unfold(monolithicExpr.propExpr, i) }
  private val indices = mutableListOf(VarIndexingFactory.indexing(0))
  private val exprs = mutableListOf<Expr<BoolType>>()
  private var kindLastIterLookup = 0
  private var iteration = 0
  private val levels = mutableListOf(VarIndexingFactory.indexing(0))

  init {
    check(bmcSolver != itpSolver || bmcSolver == null) { "Use distinct solvers for BMC and IMC!" }
    check(bmcSolver != indSolver || bmcSolver == null) { "Use distinct solvers for BMC and KInd!" }
    check(itpSolver != indSolver || itpSolver == null) { "Use distinct solvers for IMC and KInd!" }
  }

  override fun check(prec: UnitPrec?): SafetyResult<PredState, Trace<ExplState, ExprAction>> {

    iteration = 0

    val isBmcEnabled = bmcEnabled() // we don't allow per-iteration setting of bmc enabledness
    bmcSolver?.add(unfoldedInitExpr)

    while (!shouldGiveUp(iteration)) {
      iteration++
      logger.write(Logger.Level.MAINSTEP, "Starting iteration $iteration\n")
      if (!kindEnabled(iteration) && imcEnabled(iteration) && bmcEnabled()) {
        logger.writeln(
          Logger.Level.INFO,
          "BMC and IMC together are inefficient; IMC includes BMC as a substep.",
        )
      }
      check((!kindEnabled(iteration)) || bmcEnabled()) {
        "K-Induction needs BMC as an external substep."
      }

      exprs.add(PathUtils.unfold(monolithicExpr.transExpr, indices.last()))

      indices.add(indices.last().add(monolithicExpr.transOffsetIndex))

      if (isBmcEnabled) {
        bmc()?.let {
          return it
        }
      }

      if (kindEnabled(iteration)) {
        if (!isBmcEnabled) {
          error("Bad configuration: induction check should always be preceded by a BMC/SAT check")
        }
        kind()?.let {
          return it
        }
        kindLastIterLookup = iteration
      }

      if (imcEnabled(iteration)) {
        itp()?.let {
          return it
        }
      }
    }
    return SafetyResult.unknown(PredState.of(extractProof()), BoundedStatistics(iteration))
  }

  private fun bmc(): SafetyResult<PredState, Trace<ExplState, ExprAction>>? {
    val bmcSolver = this.bmcSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting BMC\n")

    if (iteration == 1) {
      WithPushPop(bmcSolver).use {
        bmcSolver.add(Not(unfoldedPropExpr(indices.first())))

        if (bmcSolver.check().isSat) {
          val trace = getTrace(bmcSolver.model)
          logger.write(
            Logger.Level.MAINSTEP,
            "CeX found in the initial state (length ${trace.length()})\n",
          )
          return SafetyResult.unsafe(
            trace,
            PredState.of(extractProof()),
            BoundedStatistics(iteration),
          )
        }
      }
    }

    bmcSolver.add(exprs.last())

    if (lfPathOnly()) { // indices contains currIndex as last()
      val loopfree = LinkedList<Expr<BoolType>>()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          loopfree += Not(allVarsSame)
        }
      }
      bmcSolver.add(loopfree)

      if (bmcSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in BMC step\n")
        return SafetyResult.safe(PredState.of(loopFreeProof()), BoundedStatistics(iteration))
      }
    }

    return WithPushPop(bmcSolver).use {
      bmcSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (bmcSolver.check().isSat) {
        val trace = getTrace(bmcSolver.model)
        logger.write(Logger.Level.MAINSTEP, "CeX found in BMC step (length ${trace.length()})\n")
        SafetyResult.unsafe(trace, PredState.of(extractProof()), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun kind(): SafetyResult<PredState, Trace<ExplState, ExprAction>>? {
    val indSolver = this.indSolver!!

    logger.write(Logger.Level.MAINSTEP, "\tStarting k-induction\n")

    exprs.subList(kindLastIterLookup, exprs.size).forEach { indSolver.add(it) }
    val allSafe = LinkedList<Expr<BoolType>>()
    indices.subList(kindLastIterLookup, indices.size - 1).forEach {
      allSafe.add(unfoldedPropExpr(it))
    }
    indSolver.add(allSafe)

    return WithPushPop(indSolver).use {
      indSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (indSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in k-induction step\n")
        SafetyResult.safe(PredState.of(kindProof()), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun itp(): SafetyResult<PredState, Trace<ExplState, ExprAction>>? {
    val itpSolver = this.itpSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting IMC\n")

    itpSolver.push()

    val a = itpSolver.createMarker()
    val b = itpSolver.createMarker()
    val pattern = itpSolver.createBinPattern(a, b)

    if (iteration == 1) {
      WithPushPop(itpSolver).use {
        itpSolver.add(a, unfoldedInitExpr)
        itpSolver.add(a, Not(unfoldedPropExpr(indices.first())))

        if (itpSolver.check().isSat) {
          val trace = getTrace(itpSolver.model)
          logger.write(
            Logger.Level.MAINSTEP,
            "CeX found in the initial state (length ${trace.length()})\n",
          )
          return SafetyResult.unsafe(
            trace,
            PredState.of(extractProof()),
            BoundedStatistics(iteration),
          )
        }
      }
    }

    itpSolver.push()

    itpSolver.add(a, unfoldedInitExpr)
    itpSolver.add(a, exprs[0])
    itpSolver.add(b, exprs.subList(1, exprs.size))

    if (lfPathOnly()) { // indices contains currIndex as last()
      itpSolver.push()
      val loopfree = LinkedList<Expr<BoolType>>()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          loopfree.add(Not(allVarsSame))
        }
      }
      itpSolver.add(a, loopfree)

      if (itpSolver.check().isUnsat) {
        itpSolver.pop()
        itpSolver.pop()
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC/BMC step\n")
        return SafetyResult.safe(PredState.of(loopFreeProof()), BoundedStatistics(iteration))
      }
      itpSolver.pop()
    }

    itpSolver.add(b, Not(unfoldedPropExpr(indices.last())))

    val status = itpSolver.check()

    if (status.isSat) {
      val trace = getTrace(itpSolver.model)
      logger.write(Logger.Level.MAINSTEP, "CeX found in IMC/BMC step (length ${trace.length()})\n")
      itpSolver.pop()
      itpSolver.pop()
      return SafetyResult.unsafe(trace, PredState.of(extractProof()), BoundedStatistics(iteration))
    }

    var img = unfoldedInitExpr
    while (itpSolver.check().isUnsat) {
      val interpolant = itpSolver.getInterpolant(pattern)
      val itpFormula =
        PathUtils.unfold(PathUtils.foldin(interpolant.eval(a), indices[1]), indices[0])
      itpSolver.pop()

      itpSolver.push()
      itpSolver.add(a, itpFormula)
      itpSolver.add(a, Not(img))
      val itpStatus = itpSolver.check()
      if (itpStatus.isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC step\n")
        itpSolver.pop()
        itpSolver.pop()
        return SafetyResult.safe(
          PredState.of(PathUtils.foldin(img, indices[0])),
          BoundedStatistics(iteration),
        )
      }
      itpSolver.pop()
      img = Or(img, itpFormula)

      itpSolver.push()
      itpSolver.add(a, itpFormula)
      itpSolver.add(a, exprs[0])
      itpSolver.add(b, exprs.subList(1, exprs.size))
      itpSolver.add(b, Not(unfoldedPropExpr(indices.last())))
    }

    itpSolver.pop()
    itpSolver.pop()
    return null
  }

  /** No loop-free path has [iteration] steps, so every reachable state is reached in fewer. */
  private fun loopFreeProof(): Expr<BoolType> =
    if (!needProof) True() else invariant(reachedWithin(iteration - 1, iteration), iteration)

  /**
   * With k = [iteration], the states reached in fewer than k steps and the ends of k-step paths
   * whose first k states satisfy the property form an inductive invariant: BMC and the induction
   * step put both inside the property, and a successor of either belongs to the second set.
   */
  private fun kindProof(): Expr<BoolType> {
    if (!needProof) return True()
    val k = iteration
    val safePathEnds = And((k until 2 * k).flatMap { listOf(propAt(it), transAt(it)) })
    return invariant(Or(reachedWithin(k - 1, 2 * k), safePathEnds), 2 * k)
  }

  /**
   * The states reached within [depth] steps, as the state at level [current]. Each disjunct
   * constrains only its own prefix, as a state need not have successors.
   */
  private fun reachedWithin(depth: Int, current: Int): Expr<BoolType> {
    var reached = sameState(depth, current)
    for (i in depth - 1 downTo 0) {
      reached = Or(sameState(i, current), And(transAt(i), reached))
    }
    return And(unfoldedInitExpr, reached)
  }

  /** [reached], a set of states at level [current], as an expression over the model's variables. */
  private fun invariant(reached: Expr<BoolType>, current: Int): Expr<BoolType> =
    ((if (interpolateProof) interpolate(reached, current) else null)
        ?: existential(reached, current))
      .also { logger.write(Logger.Level.VERBOSE, "Bounded proof: %s\n", it) }

  /**
   * An interpolant of [reached] against the states that violate the property within one step, which
   * [reached] excludes as it is an invariant; kept only if [reached] implies it. A longer horizon
   * would constrain more locations, but makes the interpolants far larger.
   */
  private fun interpolate(reached: Expr<BoolType>, current: Int): Expr<BoolType>? {
    val solver = itpSolver ?: return null
    val violating = Or(Not(propAt(current)), And(transAt(current), Not(propAt(current + 1))))
    val indexing = level(current)
    return try {
      val interpolant =
        WithPushPop(solver).use {
          val a = solver.createMarker()
          val b = solver.createMarker()
          solver.add(a, reached)
          solver.add(b, violating)
          val status = solver.check()
          if (!status.isUnsat) {
            logger.write(
              Logger.Level.INFO,
              "Bounded proof not separated from violations: $status\n",
            )
            return null
          }
          solver.getInterpolant(solver.createBinPattern(a, b)).eval(a)
        }
      val shared =
        ExprUtils.getIndexedConstants(interpolant).all { it.index == indexing.get(it.varDecl) }
      if (!shared || !implies(solver, reached, interpolant)) {
        logger.write(Logger.Level.INFO, "Discarding an invalid interpolant: $interpolant\n")
        return null
      }
      PathUtils.foldin(interpolant, indexing)
    } catch (e: InterruptedException) {
      throw e
    } catch (e: Exception) {
      logger.write(Logger.Level.INFO, "Interpolating the bounded proof failed: $e\n")
      null
    }
  }

  private fun implies(solver: ItpSolver, a: Expr<BoolType>, b: Expr<BoolType>): Boolean =
    WithPushPop(solver).use {
      val marker = solver.createMarker()
      solver.add(marker, a)
      solver.add(marker, Not(b))
      solver.check().isUnsat
    }

  /** [reached] with the states of other levels as fresh variables, unique to this proof. */
  private fun existential(reached: Expr<BoolType>, current: Int): Expr<BoolType> {
    val indexing = level(current)
    val prefix = "__bounded${proofIds.incrementAndGet()}_"
    val others =
      ExprUtils.getIndexedConstants(reached).filter { it.index != indexing.get(it.varDecl) }
    val renamed =
      ExprUtils.changeDecls(reached, others.associateWith { Var(prefix + it.name, it.type) })
    return PathUtils.foldin(renamed, indexing)
  }

  /** The indexing of the [n]th state of an unrolling. */
  private fun level(n: Int): VarIndexing {
    while (levels.size <= n) levels.add(levels.last().add(monolithicExpr.transOffsetIndex))
    return levels[n]
  }

  private fun transAt(n: Int) = PathUtils.unfold(monolithicExpr.transExpr, level(n))

  private fun propAt(n: Int) = unfoldedPropExpr(level(n))

  /** Floats are compared by representation, so that NaN equals itself. */
  @Suppress("UNCHECKED_CAST")
  private fun sameState(n: Int, m: Int): Expr<BoolType> =
    And(
      vars.map {
        val left = PathUtils.unfold(it.ref, level(n))
        val right = PathUtils.unfold(it.ref, level(m))
        if (it.type is FpType) FpAssign(left as Expr<FpType>, right as Expr<FpType>)
        else Eq(left, right)
      }
    )

  private fun extractProof(): Expr<BoolType>? =
    if (needProof) {
      // we enumerate all states explored by previous iteration of BMC
      val expr =
        And(
          exprs.subList(0, exprs.size - 1) +
            //                  loopfree.subList(0, loopfree.size - 1) +
            unfoldedInitExpr
        )
      extractModel(expr, indices.subList(0, indices.size - 1))
    } else {
      True()
    }

  private fun getTrace(model: Valuation): Trace<ExplState, ExprAction> {
    val stateList = LinkedList<ExplState>()
    val actionList = LinkedList<ExprAction>()
    var lastValuation: Valuation? = null
    for (i in indices) {
      val valuation = PathUtils.extractValuation(model, i, vars)
      stateList.add(ExplState.of(valuation))
      if (lastValuation != null) {
        actionList.add(monolithicExpr.action())
      }
      lastValuation = valuation
    }
    return Trace.of(stateList, actionList)
  }

  private fun extractModel(
    expr: Expr<BoolType>,
    indices: List<VarIndexing> = this.indices,
  ): Expr<BoolType> {
    val consts = ExprUtils.getIndexedConstants(expr)
    val map = consts.associateWith { Var(it.name, it.type) }
    val variants =
      Or(
        indices.map {
          And(
            consts
              .filter { f -> it.get(f.varDecl) == f.index }
              .map { Eq(it.varDecl.ref, map[it]!!.ref) }
          )
        }
      )
    return And(ExprUtils.changeDecls(expr, map), variants)
  }

  private companion object {
    val proofIds = AtomicInteger()
  }
}
