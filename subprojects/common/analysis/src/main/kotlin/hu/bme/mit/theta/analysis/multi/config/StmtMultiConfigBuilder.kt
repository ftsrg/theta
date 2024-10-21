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

package hu.bme.mit.theta.analysis.multi.config

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.multi.MultiPrec
import hu.bme.mit.theta.analysis.multi.RefToMultiPrec
import hu.bme.mit.theta.analysis.multi.builder.MultiBuilderResultPOJO
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAction
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiLts
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.UCSolver
import java.util.function.Predicate

sealed class StmtMultiConfigBuilder<LState : ExprState, RState : ExprState, DataState : ExprState, LControl : ExprState, RControl : ExprState, LAction : StmtAction, RAction : StmtAction, R : Refutation, LPrec : Prec, RPrec : Prec, DataPrec : Prec, LControlPrec : Prec, RControlPrec : Prec>(
    private val product: MultiBuilderResultPOJO<LState, RState, DataState, LControl, RControl, LAction, RAction, LPrec, RPrec, DataPrec, LControlPrec, RControlPrec, ExprMultiState<LControl, RControl, DataState>, ExprMultiState<LControl, RControl, UnitState>, StmtMultiAction<LAction, RAction>, StmtMultiLts<LState, RState, DataState, LControl, RControl, LAction, RAction>>,
    val prop: Expr<BoolType>,
    val target: Predicate<ExprMultiState<LControl, RControl, DataState>>,
    private val lRefToPrec: RefutationToPrec<LPrec, R>,
    private val rRefToPrec: RefutationToPrec<RPrec, R>,
    private val dRefToPrec: RefutationToPrec<DataPrec, R>,
    private val lInitPrec: LPrec,
    private val rInitPrec: RPrec,
    private val dInitPrec: DataPrec,
    val solverFactory: SolverFactory,
    val logger: Logger,
    val pruneStrategy: PruneStrategy = PruneStrategy.FULL
) {

    abstract fun getTraceChecker(): ExprTraceChecker<R>

    fun build(): MultiConfig<DataState, LControl, RControl, LAction, RAction, LPrec, RPrec, DataPrec, ExprMultiState<LControl, RControl, DataState>, StmtMultiAction<LAction, RAction>> {
        val argBuilder = ArgBuilder.create(product.lts, product.side.analysis, target)
        val abstractor = BasicArgAbstractor.builder(argBuilder).build()
        val traceChecker = getTraceChecker()
        val precRefiner =
            JoiningPrecRefiner.create<ExprMultiState<LControl, RControl, DataState>, StmtMultiAction<LAction, RAction>, MultiPrec<LPrec, RPrec, DataPrec>, R>(
                RefToMultiPrec(lRefToPrec, rRefToPrec, dRefToPrec)
            )
        val refiner = SingleExprTraceRefiner.create(traceChecker, precRefiner, pruneStrategy, logger)
        return MultiConfig(
            ArgCegarChecker.create(abstractor, refiner), MultiPrec(lInitPrec, rInitPrec, dInitPrec)
        )
    }

    class ItpStmtMultiConfigBuilder<LState : ExprState, RState : ExprState, DataState : ExprState, LControl : ExprState, RControl : ExprState, LAction : StmtAction, RAction : StmtAction, LPrec : Prec, RPrec : Prec, DataPrec : Prec, LControlPrec : Prec, RControlPrec : Prec>(
        product: MultiBuilderResultPOJO<LState, RState, DataState, LControl, RControl, LAction, RAction, LPrec, RPrec, DataPrec, LControlPrec, RControlPrec, ExprMultiState<LControl, RControl, DataState>, ExprMultiState<LControl, RControl, UnitState>, StmtMultiAction<LAction, RAction>, StmtMultiLts<LState, RState, DataState, LControl, RControl, LAction, RAction>>,
        prop: Expr<BoolType>,
        target: Predicate<ExprMultiState<LControl, RControl, DataState>>,
        lRefToPrec: RefutationToPrec<LPrec, ItpRefutation>,
        rRefToPrec: RefutationToPrec<RPrec, ItpRefutation>,
        dRefToPrec: RefutationToPrec<DataPrec, ItpRefutation>,
        lInitPrec: LPrec,
        rInitPrec: RPrec,
        dInitPrec: DataPrec,
        solverFactory: SolverFactory,
        logger: Logger,
        pruneStrategy: PruneStrategy = PruneStrategy.FULL,
        private val traceCheckerType: TraceCheckerType = TraceCheckerType.SEQ_ITP
    ) : StmtMultiConfigBuilder<LState, RState, DataState, LControl, RControl, LAction, RAction, ItpRefutation, LPrec, RPrec, DataPrec, LControlPrec, RControlPrec>(
        product,
        prop,
        target,
        lRefToPrec,
        rRefToPrec,
        dRefToPrec,
        lInitPrec,
        rInitPrec,
        dInitPrec,
        solverFactory,
        logger,
        pruneStrategy
    ) {

        enum class TraceCheckerType(
            val generator: (init: Expr<BoolType>, target: Expr<BoolType>, solver: ItpSolver) -> ExprTraceChecker<ItpRefutation>
        ) {

            SEQ_ITP(ExprTraceSeqItpChecker::create), FW_BIN(ExprTraceFwBinItpChecker::create), BW_BIN(
                ExprTraceBwBinItpChecker::create
            )
        }

        override fun getTraceChecker(): ExprTraceChecker<ItpRefutation> = traceCheckerType.generator(
            BoolExprs.True(), prop, solverFactory.createItpSolver()
        )
    }

    class VarsStmtMultiConfigBuilder<LState : ExprState, RState : ExprState, DataState : ExprState, LControl : ExprState, RControl : ExprState, LAction : StmtAction, RAction : StmtAction, LPrec : Prec, RPrec : Prec, DataPrec : Prec, LControlPrec : Prec, RControlPrec : Prec>(
        product: MultiBuilderResultPOJO<LState, RState, DataState, LControl, RControl, LAction, RAction, LPrec, RPrec, DataPrec, LControlPrec, RControlPrec, ExprMultiState<LControl, RControl, DataState>, ExprMultiState<LControl, RControl, UnitState>, StmtMultiAction<LAction, RAction>, StmtMultiLts<LState, RState, DataState, LControl, RControl, LAction, RAction>>,
        prop: Expr<BoolType>,
        target: Predicate<ExprMultiState<LControl, RControl, DataState>>,
        lRefToPrec: RefutationToPrec<LPrec, VarsRefutation>,
        rRefToPrec: RefutationToPrec<RPrec, VarsRefutation>,
        dRefToPrec: RefutationToPrec<DataPrec, VarsRefutation>,
        lInitPrec: LPrec,
        rInitPrec: RPrec,
        dInitPrec: DataPrec,
        solverFactory: SolverFactory,
        logger: Logger,
        pruneStrategy: PruneStrategy = PruneStrategy.FULL,
        private val traceCheckerType: TraceCheckerType = TraceCheckerType.UNSAT_CORE
    ) : StmtMultiConfigBuilder<LState, RState, DataState, LControl, RControl, LAction, RAction, VarsRefutation, LPrec, RPrec, DataPrec, LControlPrec, RControlPrec>(
        product,
        prop,
        target,
        lRefToPrec,
        rRefToPrec,
        dRefToPrec,
        lInitPrec,
        rInitPrec,
        dInitPrec,
        solverFactory,
        logger,
        pruneStrategy
    ) {

        enum class TraceCheckerType(
            val generator: (init: Expr<BoolType>, target: Expr<BoolType>, solver: UCSolver) -> ExprTraceChecker<VarsRefutation>
        ) {

            UNSAT_CORE(ExprTraceUnsatCoreChecker::create)
        }

        override fun getTraceChecker(): ExprTraceChecker<VarsRefutation> = traceCheckerType.generator(
            BoolExprs.True(), prop, solverFactory.createUCSolver()
        )
    }

}
