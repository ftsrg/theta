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
package hu.bme.mit.theta.analysis.algorithm.bounded;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class MonolithicExprCegarChecker<W extends Proof>
        implements SafetyChecker<W, Trace<? extends ExprState, ? extends ExprAction>, PredPrec> {
    private final MonolithicExpr model;
    private final Function<
                    MonolithicExpr,
                    SafetyChecker<
                            W,
                            ? extends Trace<? extends ExprState, ? extends ExprAction>,
                            UnitPrec>>
            checkerFactory;

    private final SolverFactory solverFactory;

    private final Logger logger;

    public MonolithicExprCegarChecker(
            MonolithicExpr model,
            Function<
                            MonolithicExpr,
                            SafetyChecker<
                                    W,
                                    ? extends Trace<? extends ExprState, ? extends ExprAction>,
                                    UnitPrec>>
                    checkerFactory,
            Logger logger,
            SolverFactory solverFactory) {
        this.model = model;
        this.checkerFactory = checkerFactory;
        this.logger = logger;
        this.solverFactory = solverFactory;
    }

    public SafetyResult<W, Trace<? extends ExprState, ? extends ExprAction>> check(
            PredPrec initPrec) {
        var predPrec =
                initPrec == null
                        ? PredPrec.of(List.of(model.getInitExpr(), model.getPropExpr()))
                        : initPrec;

        while (true) {
            logger.write(Logger.Level.SUBSTEP, "Current prec: %s\n", predPrec);

            final var abstractMonolithicExpr =
                    AbstractMonolithicExprKt.createAbstract(model, predPrec);
            final var checker = checkerFactory.apply(abstractMonolithicExpr);

            final var result = checker.check();
            if (result.isSafe()) {
                logger.write(Logger.Level.MAINSTEP, "Model is safe, stopping CEGAR");
                return SafetyResult.safe(result.getProof());
            } else {
                Preconditions.checkState(result.isUnsafe());
                final Trace<? extends ExprState, ? extends ExprAction> trace =
                        result.asUnsafe().getCex();

                final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker =
                        ExprTraceFwBinItpChecker.create(
                                model.getInitExpr(),
                                Not(model.getPropExpr()),
                                solverFactory.createItpSolver());

                if (trace != null) {
                    logger.write(Logger.Level.VERBOSE, "\tFound trace: %s\n", trace);
                    final ExprTraceStatus<ItpRefutation> concretizationResult =
                            exprTraceFwBinItpChecker.check(trace);
                    if (concretizationResult.isFeasible()) {
                        logger.write(Logger.Level.MAINSTEP, "Model is unsafe, stopping CEGAR\n");

                        final var valuations =
                                concretizationResult.asFeasible().getValuations().getStates();
                        final List<ExprState> states = new ArrayList<>();
                        final List<ExprAction> actions = new ArrayList<>();
                        for (int i = 0; i < valuations.size(); ++i) {
                            states.add(model.getValToState().invoke(valuations.get(i)));
                            if (i > 0) {
                                actions.add(
                                        model.getBiValToAction()
                                                .invoke(valuations.get(i - 1), valuations.get(i)));
                            }
                        }

                        return SafetyResult.Unsafe.unsafe(
                                Trace.of(states, actions), result.getProof());
                    } else {
                        final var ref = concretizationResult.asInfeasible().getRefutation();
                        final var newPred = ref.get(ref.getPruneIndex());
                        for (var splitPred : ExprSplitters.conjuncts().apply(newPred)) {
                            final var newPrec = PredPrec.of(splitPred);
                            predPrec = predPrec.join(newPrec);
                        }

                        logger.write(Logger.Level.INFO, "Added new predicate " + newPred + "\n");
                    }
                }
            }
        }
    }
}
