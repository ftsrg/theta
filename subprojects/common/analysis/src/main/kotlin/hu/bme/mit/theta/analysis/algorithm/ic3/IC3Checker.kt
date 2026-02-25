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

package hu.bme.mit.theta.analysis.algorithm.ic3

import hu.bme.mit.theta.analysis.*
import hu.bme.mit.theta.analysis.algorithm.*
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.*
import hu.bme.mit.theta.core.type.booltype.*
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.*
import hu.bme.mit.theta.solver.utils.WithPushPop
import java.util.*
import java.util.function.BiFunction
import java.util.function.Function

class IC3Checker<S : ExprState, A : ExprAction>(
  private val monolithicExpr: MonolithicExpr,
  private val solverFactory: SolverFactory,
  private val valToState: Function<Valuation, S>,
  private val biValToAction: BiFunction<Valuation, Valuation, A>,
  private val formerFramesOpt: Boolean = true,
  private val unSatOpt: Boolean = true,
  private val notBOpt: Boolean = true,
  private val propagateOpt: Boolean = true,
  private val filterOpt: Boolean = true,
  private val propertyOpt: Boolean = true,
  private val logger: Logger
) : SafetyChecker<EmptyProof, Trace<S, A>, UnitPrec> {
  private val frames = mutableListOf<Frame>()
  private val solver: UCSolver = solverFactory.createUCSolver()
  private var currentFrameNumber = 0
  val valuations: MutableList<MutableValuation> = mutableListOf()

  init {
    frames.add(Frame(null, solver, monolithicExpr))
    frames[0].refine(monolithicExpr.initExpr)
  }
  override fun check(prec: UnitPrec): SafetyResult<EmptyProof, Trace<S, A>> {
    checkFirst()?.let {
      val result = SafetyResult.unsafe(it, EmptyProof.getInstance())
      logger.writeln(Logger.Level.RESULT, result.toString())
      return result
    }

  }
  fun checkFirst(): Trace<ExplState, ExprAction>? {
    //check if initial state violates or not the property
    WithPushPop(solver).use {
      solver.track(
        PathUtils.unfold(
          monolithicExpr.initExpr,
          VarIndexingFactory.indexing(0)
        )
      )

      solver.track(
        PathUtils.unfold(
          Not(monolithicExpr.propExpr),
          VarIndexingFactory.indexing(0)
        )
      )

      if (solver.check().isSat) {
        return Trace.of(
          listOf(
            ExplState.of(
              PathUtils.extractValuation(
                solver.model,
                VarIndexingFactory.indexing(0),
                monolithicExpr.vars
              )
            )
          ),
          emptyList()
        )
      }
    }
  //check, if the error states are reachable in one transition step
    if (propertyOpt) {
      WithPushPop(solver).use {

        solver.track(
          PathUtils.unfold(
            monolithicExpr.initExpr,
            VarIndexingFactory.indexing(0)
          )
        )

        solver.track(
          PathUtils.unfold(
            monolithicExpr.transExpr,
            VarIndexingFactory.indexing(0)
          )
        )

        solver.track(
          PathUtils.unfold(
            Not(monolithicExpr.propExpr),
            monolithicExpr.transOffsetIndex
          )
        )

        if (solver.check().isSat) {
          return Trace.of(
            listOf(
              ExplState.of(
                PathUtils.extractValuation(
                  solver.model,
                  VarIndexingFactory.indexing(0),
                  monolithicExpr.vars
                )
              ),
              ExplState.of(
                PathUtils.extractValuation(
                  solver.model,
                  monolithicExpr.transOffsetIndex,
                  monolithicExpr.vars
                )
              )
            ),
            listOf(monolithicExpr.action())
          )
        } else {
          return null
        }
      }
    }

    return null
  }

}