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

import com.beust.jcommander.Parameter
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory
import hu.bme.mit.theta.solver.z3.Z3SolverManager
import hu.bme.mit.theta.xcfa.model.XCFA
import java.nio.file.Path

data class XcfaCegarConfig(
        @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
        var solverHome: String = SmtLibSolverManager.HOME.toAbsolutePath().toString(),
        @Parameter(names = ["--abstraction-solver"], description = "Abstraction solver name")
        var abstractionSolver: String = "Z3",
        @Parameter(names = ["--validate-abstraction-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
        var validateAbstractionSolver: Boolean = false,
        @Parameter(names = ["--domain"], description = "Abstraction domain")
        var domain: Domain = Domain.EXPL,
        @Parameter(names = ["--maxenum"], description = "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.")
        var maxEnum: Int = 0,
        @Parameter(names = ["--search"], description = "Search strategy")
        var search: Search = Search.ERR,
        @Parameter(names = ["--initprec"], description = "Initial precision")
        var initPrec: InitPrec = InitPrec.EMPTY,
        @Parameter(names = ["--refinement-solver"], description = "Refinement solver name")
        var refinementSolver: String = "Z3",
        @Parameter(names = ["--validate-refinement-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
        var validateRefinementSolver: Boolean = false,
        @Parameter(names = ["--refinement"], description = "Refinement strategy")
        var refinement: Refinement = Refinement.SEQ_ITP,
        @Parameter(names = ["--predsplit"], description = "Predicate splitting (for predicate abstraction)")
        var exprSplitter: ExprSplitterOptions = ExprSplitterOptions.WHOLE,
        @Parameter(names = ["--prunestrategy"], description = "Strategy for pruning the ARG after refinement")
        var pruneStrategy: PruneStrategy = PruneStrategy.LAZY,
        @Parameter(names = ["--loglevel-cegar"], description = "Detailedness of logging")
        var logLevel: Logger.Level = Logger.Level.RESULT
) {
    @Suppress("UNCHECKED_CAST")
    private fun getCegarChecker(xcfa: XCFA): CegarChecker<ExprState, ExprAction, Prec> {
        val logger = ConsoleLogger(logLevel)
        registerAllSolverManagers(solverHome, logger)
        val abstractionSolverFactory: SolverFactory = getSolver(abstractionSolver, validateAbstractionSolver)
        val refinementSolverFactory: SolverFactory = getSolver(refinementSolver, validateRefinementSolver)

        val abstractor: Abstractor<ExprState, ExprAction, Prec> = domain.abstractor(
                xcfa,
                abstractionSolverFactory.createSolver(),
                maxEnum,
                search.getComp(xcfa),
                refinement.stopCriterion,
                logger
        ) as Abstractor<ExprState, ExprAction, Prec>

        val ref: ExprTraceChecker<Refutation> =
                refinement.refiner(refinementSolverFactory)
                        as ExprTraceChecker<Refutation>
        val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
                domain.itpPrecRefiner(exprSplitter.exprSplitter)
                        as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
        val refiner: Refiner<ExprState, ExprAction, Prec> =
                if (refinement == Refinement.MULTI_SEQ)
                    MultiExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)
                else
                    SingleExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)

        return CegarChecker.create(abstractor, refiner, logger)
    }
    fun check(xcfa: XCFA): SafetyResult<ExprState, ExprAction> =
            getCegarChecker(xcfa).check(domain.initPrec(xcfa, initPrec))
}

private fun getSolver(name: String, validate: Boolean) = if (validate) {
    SolverValidatorWrapperFactory.create(name)
} else {
    SolverManager.resolveSolverFactory(name)
}

private fun registerAllSolverManagers(home: String, logger: Logger) {
//        CpuTimeKeeper.saveSolverTimes()
    SolverManager.closeAll()
    // register solver managers
    SolverManager.registerSolverManager(Z3SolverManager.create())
    if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
        val homePath = Path.of(home)
        val smtLibSolverManager: SmtLibSolverManager = SmtLibSolverManager.create(homePath, logger)
        SolverManager.registerSolverManager(smtLibSolverManager)
    }
}