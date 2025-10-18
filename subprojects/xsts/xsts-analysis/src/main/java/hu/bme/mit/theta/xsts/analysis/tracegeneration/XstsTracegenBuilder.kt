/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis.tracegeneration

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.CegarTraceGenerationChecker.Companion.create
import hu.bme.mit.theta.analysis.expl.*
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.*
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder
import hu.bme.mit.theta.xsts.analysis.initprec.XstsAllVarsInitPrec
import hu.bme.mit.theta.xsts.analysis.initprec.XstsVarListInitPrec
import java.io.File
import java.io.IOException
import java.util.*
import java.util.function.Predicate

class XstsTracegenBuilder(
  private val solverFactory: SolverFactory,
  private val transitionCoverage: Boolean,
) {
  private var logger: Logger = NullLogger.getInstance()
  private var varFile: File? = null
  private var abstraction = TracegenerationAbstraction.NONE
  private var getFullTraces = false

  fun logger(logger: Logger): XstsTracegenBuilder {
    this.logger = logger
    return this
  }

  fun setVarFile(filename: String?): XstsTracegenBuilder {
    if (filename != null) {
      this.varFile = File(filename)
    }
    return this
  }

  fun setAbstraction(abstraction: TracegenerationAbstraction): XstsTracegenBuilder {
    this.abstraction = abstraction
    return this
  }

  private fun buildExpl(xsts: XSTS): XstsTracegenConfig<out State, out Action, out Prec> {
    val solver2 =
      solverFactory.createSolver() // abstraction // TODO handle separate solvers in a nicer way

    val analysis = XstsAnalysis.create(ExplAnalysis.create(solver2, BoolExprs.True()))
    val lts = XstsLts.create(xsts, XstsStmtOptimizer.create(ExplStmtOptimizer.getInstance()))

    val negProp: Expr<BoolType> = BoolExprs.Not(xsts.prop)
    val target: Predicate<XstsState<ExplState>?> =
      XstsStatePredicate(ExplStatePredicate(negProp, solver2))
    val argBuilder = ArgBuilder.create(lts, analysis, target, true)

    if (abstraction == TracegenerationAbstraction.VARLIST) {
      val abstractor: BasicArgAbstractor<XstsState<ExplState>, XstsAction, ExplPrec> =
        BasicArgAbstractor.builder(argBuilder)
          .waitlist(PriorityWaitlist.create(XstsConfigBuilder.Search.DFS.comparator))
          .stopCriterion(StopCriterions.fullExploration())
          .logger(logger)
          .build()

      val tracegenChecker = create(logger, abstractor, getFullTraces)

      assert(varFile != null)
      try {
        Scanner(varFile).use { scanner ->
          val varNamesToAdd: MutableSet<String> = HashSet()
          val varsToAdd: MutableSet<VarDecl<*>> = HashSet()
          while (scanner.hasNext()) {
            varNamesToAdd.add(scanner.nextLine().trim { it <= ' ' })
          }
          val vars = xsts.vars
          for (`var` in vars) {
            if (varNamesToAdd.contains(`var`.name)) {
              varsToAdd.add(`var`)
            }
          }
          Preconditions.checkState(varNamesToAdd.size == varsToAdd.size)
          return XstsTracegenConfig.create(
            tracegenChecker,
            XstsVarListInitPrec(varsToAdd)
              .setTransitionCoverage(transitionCoverage)
              .createExpl(xsts),
          )
        }
      } catch (e: IOException) {
        throw RuntimeException(e)
      }
    } else {
      assert(abstraction == TracegenerationAbstraction.NONE)
      val abstractor: BasicArgAbstractor<XstsState<ExplState>, XstsAction, ExplPrec> =
        BasicArgAbstractor.builder(argBuilder)
          .waitlist(PriorityWaitlist.create(XstsConfigBuilder.Search.DFS.comparator))
          .stopCriterion(StopCriterions.fullExploration())
          .logger(logger)
          .build()

      val tracegenChecker = create(logger, abstractor, getFullTraces)
      return XstsTracegenConfig.create(tracegenChecker, XstsAllVarsInitPrec().createExpl(xsts))
    }
  }

  /*
  private fun buildPred(xsts: XSTS) : XstsTracegenConfig<out ExprState?, out ExprAction?, out PredPrec?> {
      assert(abstraction==TracegenerationAbstraction.AUTOPRED)
      val lts = XstsLts.create(xsts, XstsStmtOptimizer.create(PredStmtOptimizer.getInstance()))
      val negProp: Expr<BoolType> = BoolExprs.Not(xsts.prop)
      val solver2 =
          solverFactory.createSolver() // abstraction // TODO handle separate solvers in a nicer way
      val target: Predicate<XstsState<PredState>?> =
          XstsStatePredicate<ExprStatePredicate, PredState>(
              ExprStatePredicate(negProp, solver2)
          )

      val analysis = XstsAnalysis.create<PredState, PredPrec>(
          PredAnalysis.create<XstsAction>(
              solver2, PredAbstractors.booleanAbstractor(solver2),
              xsts.initFormula
          )
      )
      val argBuilder = ArgBuilder.create(lts, analysis, target, true)

      val abstractor: Abstractor<XstsState<PredState>?, XstsAction?, PredPrec?> =
          BasicArgAbstractor.builder(argBuilder)
              .waitlist(PriorityWaitlist.create(XstsConfigBuilder.Search.DFS.comparator))
              .stopCriterion(StopCriterions.fullExploration())
              .logger(logger).build()
      val tracegenChecker = create(logger, abstractor)
      return XstsTracegenConfig.create(
          tracegenChecker,
          XstsTracegenPredInitPrec().createPred(xsts)
      )
  }
  */

  fun build(xsts: XSTS): XstsTracegenConfig<out State, out Action, out Prec> {
    val solver2 =
      solverFactory.createSolver() // abstraction // TODO handle separate solvers in a nicer way

    val analysis = XstsAnalysis.create(ExplAnalysis.create(solver2, BoolExprs.True()))
    val lts = XstsLts.create(xsts, XstsStmtOptimizer.create(ExplStmtOptimizer.getInstance()))

    val negProp: Expr<BoolType> = BoolExprs.Not(xsts.prop)
    val target: Predicate<XstsState<ExplState>?> =
      XstsStatePredicate(ExplStatePredicate(negProp, solver2))
    val argBuilder = ArgBuilder.create(lts, analysis, target, true)

    if (abstraction == TracegenerationAbstraction.VARLIST) {
      return buildExpl(xsts)
    } /*else if (abstraction==TracegenerationAbstraction.AUTOPRED) {
          return buildPred(xsts)
      } */ else {
      assert(abstraction == TracegenerationAbstraction.NONE)
      return buildExpl(xsts)
    }
  }

  fun setGetFullTraces(getFullTraces: Boolean): XstsTracegenBuilder {
    this.getFullTraces = getFullTraces
    return this
  }
}
