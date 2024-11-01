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
package hu.bme.mit.theta.analysis.algorithm.loopchecker;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.asg.ASG;
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.ASGAbstractor;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopcheckerSearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.SingleASGTraceRefiner;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.analysis.utils.AsgVisualizer;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaAnalysis;
import hu.bme.mit.theta.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.cfa.analysis.prec.RefutationToGlobalCfaPrec;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.ItpSolver;
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Objects;
import java.util.function.Predicate;
import kotlin.Unit;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class ASGCegarVerifierTest {

    private static Solver abstractionSolver;
    private static ItpSolver itpSolver;
    private static SolverFactory solverFactory;
    private static Logger logger;

    @BeforeClass
    public static void init() {
        abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
        itpSolver = Z3LegacySolverFactory.getInstance().createItpSolver();
        solverFactory = Z3LegacySolverFactory.getInstance();
        logger = new ConsoleLogger(Logger.Level.INFO);
    }

    @Parameterized.Parameter public String fileName;

    @Parameterized.Parameter(1)
    public String propFileName;

    @Parameterized.Parameter(2)
    public String acceptingLocationName;

    @Parameterized.Parameter(3)
    public boolean result;

    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"counter3.xsts", "x_eq_3.prop", "", false},
                    {"counter6to7.xsts", "x_eq_7.prop", "", true},
                    {"counter6to7.cfa", "", "IS6", true},
                    {"counter2to3.cfa", "", "IS3", true},
                    {"counter6to7.xsts", "x_eq_6.prop", "", true},
                    {"infinitehavoc.xsts", "x_eq_7.prop", "", true},
                    {"colors.xsts", "currentColor_eq_Green.prop", "", true},
                    {"counter5.xsts", "x_eq_5.prop", "", true},
                    {"forever5.xsts", "x_eq_5.prop", "", true},
                    {"counter6to7.xsts", "x_eq_5.prop", "", false}
                });
    }

    @Test
    public void test() throws IOException {
        if (propFileName.isBlank() && !acceptingLocationName.isBlank()) testWithCfa();
        if (!propFileName.isBlank() && acceptingLocationName.isBlank()) testWithXsts();
    }

    private void testWithXsts() throws IOException {
        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream(String.format("src/test/resources/xsts/%s", fileName)),
                        new FileInputStream(
                                String.format("src/test/resources/prop/%s", propFileName)))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }
        final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis =
                XstsAnalysis.create(
                        PredAnalysis.create(
                                abstractionSolver,
                                PredAbstractors.booleanSplitAbstractor(abstractionSolver),
                                xsts.getInitFormula()));
        final LTS<XstsState<PredState>, XstsAction> lts =
                XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
        final Predicate<XstsState<PredState>> statePredicate =
                new XstsStatePredicate<>(new ExprStatePredicate(xsts.getProp(), abstractionSolver));
        final AcceptancePredicate<XstsState<PredState>, XstsAction> target =
                new AcceptancePredicate<>(statePredicate::test, Unit.INSTANCE);
        logger.write(Logger.Level.MAINSTEP, "Verifying %s%n", xsts.getProp());
        LoopcheckerSearchStrategy.getEntries()
                .forEach(
                        lStrat -> {
                            ASGTraceCheckerStrategy.getEntries()
                                    .forEach(
                                            strat -> {
                                                var abstractor =
                                                        new ASGAbstractor<>(
                                                                analysis, lts, target, lStrat,
                                                                logger);
                                                final Refiner<
                                                                PredPrec,
                                                                ASG<
                                                                        XstsState<PredState>,
                                                                        XstsAction>,
                                                                ASGTrace<
                                                                        XstsState<PredState>,
                                                                        XstsAction>>
                                                        refiner =
                                                                new SingleASGTraceRefiner<>(
                                                                        strat,
                                                                        solverFactory,
                                                                        JoiningPrecRefiner.create(
                                                                                new ItpRefToPredPrec(
                                                                                        ExprSplitters
                                                                                                .atoms())),
                                                                        logger,
                                                                        xsts.getInitFormula());
                                                final CegarChecker<
                                                                PredPrec,
                                                                ASG<
                                                                        XstsState<PredState>,
                                                                        XstsAction>,
                                                                ASGTrace<
                                                                        XstsState<PredState>,
                                                                        XstsAction>>
                                                        verifier =
                                                                CegarChecker.create(
                                                                        abstractor,
                                                                        refiner,
                                                                        logger,
                                                                        new AsgVisualizer<>(
                                                                                Objects::toString,
                                                                                Objects::toString));

                                                final PredPrec precision = PredPrec.of();
                                                var result = verifier.check(precision);
                                                Assert.assertEquals(this.result, result.isUnsafe());
                                            });
                        });
    }

    private void testWithCfa() throws IOException {
        final CFA cfa =
                CfaDslManager.createCfa(
                        new FileInputStream(String.format("src/test/resources/cfa/%s", fileName)));
        final CfaLts lts = CfaConfigBuilder.Encoding.SBE.getLts(null);
        final Analysis<CfaState<PredState>, CfaAction, CfaPrec<PredPrec>> analysis =
                CfaAnalysis.create(
                        cfa.getInitLoc(),
                        PredAnalysis.create(
                                abstractionSolver,
                                PredAbstractors.booleanSplitAbstractor(abstractionSolver),
                                True()));
        final Predicate<CfaState<PredState>> statePredicate =
                cfaState -> cfaState.getLoc().getName().equals(acceptingLocationName);
        final AcceptancePredicate<CfaState<PredState>, CfaAction> target =
                new AcceptancePredicate<>(statePredicate::test, Unit.INSTANCE);
        final RefutationToPrec<PredPrec, ItpRefutation> refToPrec =
                new ItpRefToPredPrec(ExprSplitters.atoms());
        final RefutationToGlobalCfaPrec<PredPrec, ItpRefutation> cfaRefToPrec =
                new RefutationToGlobalCfaPrec<>(refToPrec, cfa.getInitLoc());
        LoopcheckerSearchStrategy.getEntries()
                .forEach(
                        lStrat -> {
                            ASGTraceCheckerStrategy.getEntries()
                                    .forEach(
                                            strat -> {
                                                var abstractor =
                                                        new ASGAbstractor<>(
                                                                analysis, lts, target, lStrat,
                                                                logger);
                                                final Refiner<
                                                                CfaPrec<PredPrec>,
                                                                ASG<CfaState<PredState>, CfaAction>,
                                                                ASGTrace<
                                                                        CfaState<PredState>,
                                                                        CfaAction>>
                                                        refiner =
                                                                new SingleASGTraceRefiner<>(
                                                                        strat,
                                                                        solverFactory,
                                                                        JoiningPrecRefiner.create(
                                                                                cfaRefToPrec),
                                                                        logger,
                                                                        True());
                                                final CegarChecker<
                                                                CfaPrec<PredPrec>,
                                                                ASG<CfaState<PredState>, CfaAction>,
                                                                ASGTrace<
                                                                        CfaState<PredState>,
                                                                        CfaAction>>
                                                        verifier =
                                                                CegarChecker.create(
                                                                        abstractor,
                                                                        refiner,
                                                                        logger,
                                                                        new AsgVisualizer<>(
                                                                                Objects::toString,
                                                                                Objects::toString));

                                                final GlobalCfaPrec<PredPrec> prec =
                                                        GlobalCfaPrec.create(PredPrec.of());
                                                var res = verifier.check(prec);
                                                Assert.assertEquals(result, res.isUnsafe());
                                            });
                        });
    }
}
