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
package hu.bme.mit.theta.analysis.algorithm.loopchecker;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.asg.ASG;
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.ASGAbstractor;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.BoundedUnrollingASGTraceCheckerStrategy;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.List;
import java.util.function.Predicate;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

public class ASGTraceCheckerTest {
    @Test
    public void testWithCounter3() throws IOException {
        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream("src/test/resources/xsts/counter3.xsts"),
                        new FileInputStream("src/test/resources/prop/x_eq_3.prop"))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }
        final SolverFactory solverFactory = Z3LegacySolverFactory.getInstance();
        final Solver abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
        final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis =
                XstsAnalysis.create(
                        PredAnalysis.create(
                                abstractionSolver,
                                PredAbstractors.booleanAbstractor(abstractionSolver),
                                xsts.getInitFormula()));
        final LTS<XstsState<PredState>, XstsAction> lts =
                XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
        final Predicate<XstsState<PredState>> statePredicate =
                new XstsStatePredicate<>(new ExprStatePredicate(xsts.getProp(), abstractionSolver));
        final AcceptancePredicate<XstsState<PredState>, XstsAction> target =
                new AcceptancePredicate<>(statePredicate::test);
        final PredPrec precision = PredPrec.of();
        final Logger logger = new ConsoleLogger(Logger.Level.DETAIL);
        final ASGAbstractor<XstsState<PredState>, XstsAction, PredPrec> abstractor =
                new ASGAbstractor<>(
                        analysis,
                        lts,
                        target,
                        LoopCheckerSearchStrategy.Companion.getDefault(),
                        logger);
        ASG<XstsState<PredState>, XstsAction> ASG = new ASG<>(target);
        abstractor.check(ASG, precision);
        ASGTrace<XstsState<PredState>, XstsAction> trace = ASG.getTraces().iterator().next();

        ASGTraceCheckerStrategy.getEntries()
                .forEach(
                        strat -> {
                            ExprTraceStatus<ItpRefutation> status =
                                    strat.check(
                                            trace, solverFactory, xsts.getInitFormula(), logger);
                            Assertions.assertTrue(status.isInfeasible());
                        });
    }

    @Test
    public void testBoundedUnrollingOnlyUnrollsFromReachableHonda() throws IOException {
        // the loop has a fixpoint only when d is false, which no reachable state satisfies
        final XSTS xsts = loadXsts("stoppingcounter.xsts", "true.prop");
        final ASGTrace<XstsState<PredState>, XstsAction> trace = findLasso(xsts);

        final ExprTraceStatus<ItpRefutation> status =
                new BoundedUnrollingASGTraceCheckerStrategy<>(
                                trace,
                                Z3LegacySolverFactory.getInstance(),
                                xsts.getInitFormula(),
                                100,
                                new ConsoleLogger(Logger.Level.INFO))
                        .check();

        Assertions.assertTrue(status.isInfeasible());
    }

    @ParameterizedTest
    @ValueSource(strings = {"toggle.xsts", "latetoggle.xsts"})
    public void testBoundedUnrollingFindsLoopClosingAfterSeveralIterations(String model)
            throws IOException {
        final XSTS xsts = loadXsts(model, "true.prop");
        final ASGTrace<XstsState<PredState>, XstsAction> trace = findLasso(xsts);

        final ExprTraceStatus<ItpRefutation> status =
                new BoundedUnrollingASGTraceCheckerStrategy<>(
                                trace,
                                Z3LegacySolverFactory.getInstance(),
                                xsts.getInitFormula(),
                                100,
                                new ConsoleLogger(Logger.Level.INFO))
                        .check();

        Assertions.assertTrue(status.isFeasible());
        final List<Valuation> valuations = status.asFeasible().getValuations().getStates();
        Assertions.assertEquals(trace.length() + 1, valuations.size());
        Assertions.assertEquals(
                BoolExprs.True(), ExprUtils.simplify(xsts.getInitFormula(), valuations.get(0)));
    }

    private static XSTS loadXsts(String xstsFile, String propFile) throws IOException {
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream("src/test/resources/xsts/" + xstsFile),
                        new FileInputStream("src/test/resources/prop/" + propFile))) {
            return XstsDslManager.createXsts(inputStream);
        }
    }

    private static ASGTrace<XstsState<PredState>, XstsAction> findLasso(XSTS xsts) {
        final Solver abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
        final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis =
                XstsAnalysis.create(
                        PredAnalysis.create(
                                abstractionSolver,
                                PredAbstractors.booleanAbstractor(abstractionSolver),
                                xsts.getInitFormula()));
        final LTS<XstsState<PredState>, XstsAction> lts =
                XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
        final Predicate<XstsState<PredState>> statePredicate =
                new XstsStatePredicate<>(new ExprStatePredicate(xsts.getProp(), abstractionSolver));
        final AcceptancePredicate<XstsState<PredState>, XstsAction> target =
                new AcceptancePredicate<>(statePredicate::test);
        final ASGAbstractor<XstsState<PredState>, XstsAction, PredPrec> abstractor =
                new ASGAbstractor<>(
                        analysis,
                        lts,
                        target,
                        LoopCheckerSearchStrategy.Companion.getDefault(),
                        NullLogger.getInstance());
        final ASG<XstsState<PredState>, XstsAction> asg = new ASG<>(target);
        abstractor.check(asg, PredPrec.of());
        return asg.getTraces().iterator().next();
    }
}
