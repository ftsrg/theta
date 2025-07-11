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
package hu.bme.mit.theta.sts.analysis;

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

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprCegarChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.aiger.AigerParser;
import hu.bme.mit.theta.sts.aiger.AigerToSts;
import hu.bme.mit.theta.sts.dsl.StsDslManager;
import hu.bme.mit.theta.sts.dsl.StsSpec;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = Parameterized.class)
public class StsAbstractMonolithicTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public boolean isSafe;

    @Parameterized.Parameters(name = "{index}: {0}, {1}")
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    //                    {"src/test/resources/hw1_false.aag", false},
                    //                    {"src/test/resources/hw2_true.aag", true},
                    //                    {"src/test/resources/boolean1.system", false},
                    //                    {"src/test/resources/boolean2.system", false},
                    {"src/test/resources/counter.system", true},
                    {"src/test/resources/counter_bad.system", false},
                    {"src/test/resources/counter_parametric.system", true},

                    //                {"src/test/resources/loop.system", true},

                    {"src/test/resources/loop_bad.system", false},
                    {"src/test/resources/multipleinitial.system", false},
                    {"src/test/resources/readerswriters.system", true},
                    {"src/test/resources/simple1.system", false},
                    {"src/test/resources/simple2.system", true},
                    {"src/test/resources/simple3.system", false},
                });
    }

    private void runTest(
            Logger logger,
            SolverFactory solverFactory,
            Function<
                            MonolithicExpr,
                            SafetyChecker<
                                    ? extends Proof,
                                    ? extends Trace<? extends ExprState, ? extends ExprAction>,
                                    UnitPrec>>
                    builder)
            throws IOException {

        final STS sts;
        if (filePath.endsWith("aag")) {
            sts = AigerToSts.createSts(AigerParser.parse(filePath));
        } else {
            final StsSpec spec = StsDslManager.createStsSpec(new FileInputStream(filePath));
            if (spec.getAllSts().size() != 1) {
                throw new UnsupportedOperationException("STS contains multiple properties.");
            }
            sts = Utils.singleElementOf(spec.getAllSts());
        }
        final MonolithicExpr monolithicExpr = StsToMonolithicExprKt.toMonolithicExpr(sts);
        var checker =
                new MonolithicExprCegarChecker(monolithicExpr, builder, logger, solverFactory);
        Assert.assertEquals(isSafe, checker.check().isSafe());
    }

    //    @Test
    //    public void testIc3() throws IOException {
    //        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);
    //        final var solverFactory = Z3LegacySolverFactory.getInstance();
    //
    //        runTest(
    //            logger,
    //            solverFactory,
    //            abstractMe -> new Ic3Checker<>(
    //                    abstractMe,
    //                    true,
    //                    solverFactory,
    //                    valuation -> abstractMe.getValToState().invoke(valuation),
    //                    (Valuation v1, Valuation v2) -> abstractMe.getBiValToAction().invoke(v1,
    // v2),
    //                    true,
    //                    true,
    //                    true,
    //                    true,
    //                    true,
    //                    true,
    //                    logger)
    //        );
    //    }
    //
    //    @Test
    //    public void testBMC() throws IOException {
    //        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);
    //        final var solverFactory = Z3LegacySolverFactory.getInstance();
    //
    //        runTest(
    //                logger,
    //                solverFactory,
    //                abstractMe -> BoundedCheckerBuilderKt.buildBMC(
    //                        abstractMe,
    //                        solverFactory.createSolver(),
    //                        val -> abstractMe.getValToState().invoke(val),
    //                        (val1, val2) ->
    //                                abstractMe.getBiValToAction().invoke(val1, val2),
    //                        logger)
    //        );
    //    }

    @Test
    public void testMdd() throws IOException {
        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);
        final var solverFactory = Z3LegacySolverFactory.getInstance();

        try (var solverPool = new SolverPool(solverFactory)) {
            runTest(
                    logger,
                    solverFactory,
                    abstractMe ->
                            MddChecker.create(
                                    abstractMe,
                                    List.copyOf(abstractMe.getVars()),
                                    solverPool,
                                    logger,
                                    MddChecker.IterationStrategy.GSAT,
                                    valuation -> abstractMe.getValToState().invoke(valuation),
                                    (Valuation v1, Valuation v2) ->
                                            abstractMe.getBiValToAction().invoke(v1, v2), true));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
}
