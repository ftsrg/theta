/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.model.XCFA

data class XcfaCegarConfig(
        val abstractorConfig: AbstractorConfig,
        val refinerConfig: RefinerConfig,
        val logger: Logger
) {
    @Suppress("UNCHECKED_CAST")
    fun getCegarChecker(xcfa: XCFA): CegarChecker<ExprState, ExprAction, Prec> {
        val abstractor: Abstractor<ExprState, ExprAction, Prec> = abstractorConfig.domain.abstractor(
                xcfa,
                abstractorConfig.abstractionSolverFactory.createSolver(),
                abstractorConfig.maxEnum,
                abstractorConfig.search.getComp(xcfa),
                refinerConfig.refinement.stopCriterion,
                abstractorConfig.logger
        ) as Abstractor<ExprState, ExprAction, Prec>

        val ref: ExprTraceChecker<Refutation> =
                refinerConfig.refinement.refiner(refinerConfig.refinementSolverFactory)
                        as ExprTraceChecker<Refutation>
        val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
                abstractorConfig.domain.itpPrecRefiner(refinerConfig.exprSplitter.exprSplitter)
                        as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
        val refiner: Refiner<ExprState, ExprAction, Prec> =
                if (refinerConfig.refinement == Refinement.MULTI_SEQ)
                    MultiExprTraceRefiner.create(ref, precRefiner, refinerConfig.pruneStrategy, refinerConfig.logger)
                else
                    SingleExprTraceRefiner.create(ref, precRefiner, refinerConfig.pruneStrategy, refinerConfig.logger)

        return CegarChecker.create(abstractor, refiner, logger)
    }
}

data class AbstractorConfig(
        val abstractionSolverFactory: SolverFactory,
        val domain: Domain,
        val maxEnum: Int,
        val search: Search,
        val initPrec: InitPrec,
        val logger: Logger
)

data class RefinerConfig(
        val refinementSolverFactory: SolverFactory,
        val refinement: Refinement,
        val exprSplitter: ExprSplitterOptions,
        val pruneStrategy: PruneStrategy,
        val logger: Logger
)