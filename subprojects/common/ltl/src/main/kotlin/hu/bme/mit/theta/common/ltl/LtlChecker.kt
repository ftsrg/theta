/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.ltl

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.ASGAbstractor
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopcheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.SingleASGTraceRefiner
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide
import hu.bme.mit.theta.analysis.multi.MultiPrec
import hu.bme.mit.theta.analysis.multi.NextSideFunctions
import hu.bme.mit.theta.analysis.multi.NextSideFunctions.Alternating
import hu.bme.mit.theta.analysis.multi.RefToMultiPrec
import hu.bme.mit.theta.analysis.multi.builder.stmt.StmtMultiBuilder
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAction
import hu.bme.mit.theta.analysis.unit.UnitInitFunc
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.analysis.utils.AsgVisualizer
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.*
import hu.bme.mit.theta.cfa.analysis.lts.CfaSbeLts
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec
import hu.bme.mit.theta.common.cfa.buchi.Ltl2BuchiTransformer
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverFactory

class LtlChecker<
  S : ExprState,
  ControlS : ExprState,
  A : StmtAction,
  P : Prec,
  ControlP : Prec,
  DataP : Prec,
  DataS : ExprState,
>(
  multiSide: MultiAnalysisSide<S, DataS, ControlS, A, P, ControlP>,
  lts: LTS<in S, A>,
  refToPrec: RefutationToPrec<P, ItpRefutation>,
  dataRefToPrec: RefutationToPrec<DataP, ItpRefutation>,
  dataAnalysis: Analysis<DataS, in CfaAction, DataP>,
  ltl: String,
  solverFactory: SolverFactory,
  logger: Logger,
  searchStrategy: LoopcheckerSearchStrategy,
  refinerStrategy: ASGTraceCheckerStrategy,
  ltl2BuchiTransformer: Ltl2BuchiTransformer,
  variables: Collection<VarDecl<*>>,
  initExpr: Expr<BoolType> = True(),
  nextSideFunction:
    NextSideFunctions.NextSideFunction<
      ControlS,
      CfaState<UnitState>,
      DataS,
      ExprMultiState<ControlS, CfaState<UnitState>, DataS>,
    > =
    Alternating(),
) :
  SafetyChecker<
    ASG<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
    ASGTrace<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
    MultiPrec<P, CfaPrec<DataP>, DataP>,
  > {
  val checker:
    CegarChecker<
      MultiPrec<P, CfaPrec<DataP>, DataP>,
      ASG<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
      ASGTrace<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
    >

  init {
    val buchiAutomaton = ltl2BuchiTransformer.transform(ltl, variables)
    val cfaAnalysis: Analysis<CfaState<DataS>, CfaAction, CfaPrec<DataP>> =
      CfaAnalysis.create(buchiAutomaton.initLoc, dataAnalysis)
    val buchiSide =
      MultiAnalysisSide(
        cfaAnalysis,
        CfaInitFunc.create(buchiAutomaton.initLoc, UnitInitFunc.getInstance()),
        ::cfaCombineStates,
        ::cfaExtractControlState,
        { it.state },
        { _ -> GlobalCfaPrec.create(UnitPrec.getInstance()) },
      )
    val product =
      StmtMultiBuilder(multiSide, lts)
        .addRightSide(buchiSide, CfaSbeLts.getInstance())
        .build(nextSideFunction, dataAnalysis.initFunc)
    val buchiRefToPrec = RefutationToGlobalCfaPrec(dataRefToPrec, buchiAutomaton.initLoc)
    val multiRefToPrec = RefToMultiPrec(refToPrec, buchiRefToPrec, dataRefToPrec)
    val multiAnalysis = product.side.analysis
    val abstractor =
      ASGAbstractor(
        multiAnalysis,
        product.lts,
        buchiPredicate(buchiAutomaton),
        searchStrategy,
        logger,
      )
    val refiner:
      SingleASGTraceRefiner<
        ExprMultiState<ControlS, CfaState<UnitState>, DataS>,
        StmtMultiAction<A, CfaAction>,
        MultiPrec<P, CfaPrec<DataP>, DataP>,
      > =
      SingleASGTraceRefiner(
        refinerStrategy,
        solverFactory,
        JoiningPrecRefiner.create(multiRefToPrec),
        logger,
        initExpr,
      )
    val visualizer =
      AsgVisualizer<
        ExprMultiState<ControlS, CfaState<UnitState>, DataS>,
        StmtMultiAction<A, CfaAction>,
      >(
        { it.toString() },
        { "" },
      )
    checker = CegarChecker.create(abstractor, refiner, logger, visualizer)
  }

  private fun buchiPredicate(
    buchiAutomaton: CFA
  ): AcceptancePredicate<
    ExprMultiState<ControlS, CfaState<UnitState>, DataS>,
    StmtMultiAction<A, CfaAction>,
  > =
    AcceptancePredicate(
      actionPredicate = { a ->
        (a?.rightAction != null &&
          a.rightAction.edges.any { e -> buchiAutomaton.acceptingEdges.contains(e) })
      }
    )

  override fun check(
    input: MultiPrec<P, CfaPrec<DataP>, DataP>
  ): SafetyResult<
    ASG<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
    ASGTrace<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
  > {
    return checker.check(input)
  }

  fun check(
    prec: P,
    dataPrec: DataP,
  ): SafetyResult<
    ASG<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
    ASGTrace<ExprMultiState<ControlS, CfaState<UnitState>, DataS>, StmtMultiAction<A, CfaAction>>,
  > {
    return check(MultiPrec(prec, GlobalCfaPrec.create(dataPrec), dataPrec))
  }
}
