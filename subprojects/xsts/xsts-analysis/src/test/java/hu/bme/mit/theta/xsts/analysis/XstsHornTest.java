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
package hu.bme.mit.theta.xsts.analysis;

import static org.junit.Assert.assertTrue;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker;
import hu.bme.mit.theta.analysis.algorithm.chc.Invariant;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.util.ChcUtilsKt;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = Parameterized.class)
public class XstsHornTest {

    private static final Path SMTLIB_HOME = SmtLibSolverManager.HOME;

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public String propPath;

    @Parameterized.Parameter(value = 2)
    public boolean safe;

    @Parameterized.Parameter(value = 3)
    public String solverString;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        "z3:4.13.0"
                    },

                    //                {"src/test/resources/model/trafficlight_v2.xsts",
                    //                        "src/test/resources/property/green_and_red.prop",
                    // true,
                    //                        "eldarica:2.1"},

                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/x_and_y.xsts",
                        "src/test/resources/property/x_geq_y.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/x_powers.xsts",
                        "src/test/resources/property/x_even.prop",
                        true,
                        "eldarica:2.1"
                    },

                    //                {"src/test/resources/model/cross_with.xsts",
                    // "src/test/resources/property/cross.prop",
                    //                        false, "eldarica:2.1"},

                    //                { "src/test/resources/model/cross_with.xsts",
                    // "src/test/resources/property/cross.prop", false, "z3:4.13.0"},

                    //                { "src/test/resources/model/cross_with.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},
                    //
                    //                {"src/test/resources/model/cross_without.xsts",
                    //                        "src/test/resources/property/cross.prop", false,
                    //                        "eldarica:2.1"},

                    //                { "src/test/resources/model/cross_without.xsts",
                    // "src/test/resources/property/cross.prop", false, "z3:4.13.0"},

                    //                { "src/test/resources/model/cross_without.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        "golem:0.5.0"
                    },

                    //                {"src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop",
                    //                        false, "eldarica:2.1"},

                    //                { "src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop", false, "z3:4.13.0"},

                    //                { "src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        "golem:0.5.0"
                    },

                    //                { "src/test/resources/model/counter50.xsts",
                    // "src/test/resources/property/x_eq_50.prop", false, "eldarica:2.1"},

                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_50.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_50.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        "golem:0.5.0"
                    },
                    //
                    //                {"src/test/resources/model/count_up_down.xsts",
                    //                        "src/test/resources/property/count_up_down.prop",
                    // false,
                    //                        "eldarica:2.1"},

                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true,
                        "z3:4.13.0"
                    },
                    //                    {
                    //                        "src/test/resources/model/count_up_down.xsts",
                    //                        "src/test/resources/property/count_up_down2.prop",
                    //                        true,
                    //                        "golem:0.5.0"
                    //                    },
                    {
                        "src/test/resources/model/bhmr2007.xsts",
                        "src/test/resources/property/bhmr2007.prop",
                        true,
                        "eldarica:2.1"
                    },

                    //                { "src/test/resources/model/bhmr2007.xsts",
                    // "src/test/resources/property/bhmr2007.prop", true, "z3:4.13.0"},

                    //                { "src/test/resources/model/bhmr2007.xsts",
                    // "src/test/resources/property/bhmr2007.prop", true,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        "golem:0.5.0"
                    },

                    //                { "src/test/resources/model/ort.xsts",
                    // "src/test/resources/property/x_gt_2.prop", false, "eldarica:2.1"},

                    //                { "src/test/resources/model/ort2.xsts",
                    // "src/test/resources/property/ort2.prop", true, "eldarica:2.1"},

                    //                { "src/test/resources/model/crossroad_composite.xsts",
                    // "src/test/resources/property/both_green.prop", true, "z3:4.13.0"}

                    //                {"src/test/resources/model/array_counter.xsts",
                    //                        "src/test/resources/property/array_10.prop", false,
                    //                        "eldarica:2.1"},

                    {
                        "src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop",
                        false,
                        "z3:4.13.0"
                    },
                    //
                    //                {"src/test/resources/model/array_counter.xsts",
                    //                        "src/test/resources/property/array_10.prop", false,
                    //                        "golem:0.5.0"},
                    //
                    //                {"src/test/resources/model/array_constant.xsts",
                    //                        "src/test/resources/property/array_constant.prop",
                    // true,
                    //                        "eldarica:2.1"},

                    {
                        "src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop",
                        true,
                        "z3:4.13.0"
                    },
                    //
                    //                {"src/test/resources/model/array_constant.xsts",
                    //                        "src/test/resources/property/array_constant.prop",
                    // true,
                    //                        "golem:0.5.0"},

                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        "golem:0.5.0"
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        "eldarica:2.1"
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        "z3:4.13.0"
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        "golem:0.5.0"
                    },

                    //                {"src/test/resources/model/loopxy.xsts",
                    // "src/test/resources/property/loopxy.prop",
                    //                        true, "z3:4.13.0"},
                    //
                    //                {"src/test/resources/model/loopxy.xsts",
                    // "src/test/resources/property/loopxy.prop",
                    //                        true, "golem:0.5.0"},
                    //
                    //                {"src/test/resources/model/loopxy.xsts",
                    // "src/test/resources/property/loopxy.prop",
                    //                        true, "eldarica:2.1"},

                    {
                        "src/test/resources/model/arraywrite_sugar.xsts",
                        "src/test/resources/property/arraywrite_sugar.prop",
                        false,
                        "eldarica:2.1"
                    },
                    //
                    //                {"src/test/resources/model/if1.xsts",
                    // "src/test/resources/property/if1.prop", true,
                    //                        "eldarica:2.1"},

                    //                {"src/test/resources/model/if2.xsts",
                    // "src/test/resources/property/if2.prop", false,
                    //                        "golem:0.5.0"}
                });
    }

    @Before
    public void installSolver() {
        if (solverString.contains("Z3") || solverString.contains("JavaSMT")) {
            return;
        }
        Assume.assumeTrue(
                OsHelper.getOs()
                        == OsHelper.OperatingSystem
                                .LINUX); // chc solvers are only properly on linux
        try (final var solverManager =
                SmtLibSolverManager.create(SMTLIB_HOME, new ConsoleLogger(Level.DETAIL))) {
            String solverVersion = SmtLibSolverManager.getSolverVersion(solverString);
            String solverName = SmtLibSolverManager.getSolverName(solverString);
            if (solverManager.managesSolver(solverString)
                    && !solverManager
                            .getInstalledVersions(solverName)
                            .contains(
                                    solverManager.getVersionString(
                                            solverName, solverVersion, false))) {
                solverManager.install(solverName, solverVersion, solverVersion, null, false);
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private static Expr<BoolType> getBody(Expr<?> func) {
        if (func instanceof FuncLitExpr<?, ?> funcLitExpr) {
            return getBody(funcLitExpr.getResult());
        } else return (Expr<BoolType>) func;
    }

    @Test(timeout = 10_000)
    public void test() throws Exception {
        final Logger logger = new ConsoleLogger(Level.SUBSTEP);
        SolverManager.registerSolverManager(
                hu.bme.mit.theta.solver.z3legacy.Z3SolverManager.create());
        SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create());
        SolverManager.registerSolverManager(SmtLibSolverManager.create(SMTLIB_HOME, logger));
        SolverManager.registerSolverManager(JavaSMTSolverManager.create());

        final SolverFactory solverFactory;
        try {
            solverFactory = SolverManager.resolveSolverFactory(solverString);
        } catch (Exception e) {
            Assume.assumeNoException(e);
            return;
        }

        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream(filePath), new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        try {
            final var relations = XstsToRelationsKt.toRelations(xsts);
            System.err.println(ChcUtilsKt.toSMT2(relations));
            final var checker = new HornChecker(relations, solverFactory, logger);
            final SafetyResult<?, ?> status = checker.check();

            if (safe) {
                assertTrue(status.isSafe());
                var safe = (Invariant) status.asSafe().getProof();
                System.err.println(
                        safe.component1().values().stream()
                                .map(XstsHornTest::getBody)
                                .reduce(BoolExprs::Or));
            } else {
                assertTrue(status.isUnsafe());
            }
        } finally {
            SolverManager.closeAll();
        }
    }
}
