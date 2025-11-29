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

import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class XstsTest {

    private static final String SOLVER_STRING = "Z3";
    private static final Path SMTLIB_HOME = SmtLibSolverManager.HOME;
    public String filePath;
    public String propPath;
    public boolean safe;
    public XstsConfigBuilder.Domain domain;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/x_and_y.xsts",
                        "src/test/resources/property/x_geq_y.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/x_powers.xsts",
                        "src/test/resources/property/x_even.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/cross_with.xsts",
                        "src/test/resources/property/cross.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    }, // TODO: this might be faulty

                    //                { "src/test/resources/model/cross_with.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.EXPL},

                    //                { "src/test/resources/model/cross_with.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/cross_without.xsts",
                        "src/test/resources/property/cross.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },

                    //                { "src/test/resources/model/cross_without.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.EXPL},

                    //                { "src/test/resources/model/cross_without.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/choices.xsts",
                        "src/test/resources/property/choices.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/literals_fullname.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/literals.xsts",
                        "src/test/resources/property/literals.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/cross3.xsts",
                        "src/test/resources/property/cross.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },

                    //                { "src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.EXPL},

                    //                { "src/test/resources/model/cross3.xsts",
                    // "src/test/resources/property/cross.prop", false,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_5.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },

                    //                { "src/test/resources/model/counter50.xsts",
                    // "src/test/resources/property/x_eq_50.prop", false,
                    // XstsConfigBuilder.Domain.PRED_CART},

                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_50.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_50.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/counter50.xsts",
                        "src/test/resources/property/x_eq_51.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/bhmr2007.xsts",
                        "src/test/resources/property/bhmr2007.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },

                    //                { "src/test/resources/model/bhmr2007.xsts",
                    // "src/test/resources/property/bhmr2007.prop", true,
                    // XstsConfigBuilder.Domain.EXPL},

                    //                { "src/test/resources/model/bhmr2007.xsts",
                    // "src/test/resources/property/bhmr2007.prop", true,
                    // XstsConfigBuilder.Domain.PROD},

                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/css2003.xsts",
                        "src/test/resources/property/css2003.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },

                    //                { "src/test/resources/model/ort.xsts",
                    // "src/test/resources/property/x_gt_2.prop", false,
                    // XstsConfigBuilder.Domain.PRED_CART},

                    //                { "src/test/resources/model/ort2.xsts",
                    // "src/test/resources/property/ort2.prop", true,
                    // XstsConfigBuilder.Domain.PRED_CART},

                    //                { "src/test/resources/model/crossroad_composite.xsts",
                    // "src/test/resources/property/both_green.prop", true,
                    // XstsConfigBuilder.Domain.EXPL}

                    {
                        "src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/loopxy.xsts",
                        "src/test/resources/property/loopxy.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL
                    },
                    {
                        "src/test/resources/model/loopxy.xsts",
                        "src/test/resources/property/loopxy.prop",
                        true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    },
                    {
                        "src/test/resources/model/loopxy.xsts",
                        "src/test/resources/property/loopxy.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/arraywrite_sugar.xsts",
                        "src/test/resources/property/arraywrite_sugar.prop",
                        false,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/if1.xsts",
                        "src/test/resources/property/if1.prop",
                        true,
                        XstsConfigBuilder.Domain.PRED_CART
                    },
                    {
                        "src/test/resources/model/if2.xsts",
                        "src/test/resources/property/if2.prop",
                        false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED
                    }
                });
    }

    @BeforeAll
    public static void installSolver() {
        if (SOLVER_STRING.contains("Z3") || SOLVER_STRING.contains("JavaSMT")) {
            return;
        }
        try (final var solverManager =
                SmtLibSolverManager.create(SMTLIB_HOME, new ConsoleLogger(Level.DETAIL))) {
            String solverVersion = SmtLibSolverManager.getSolverVersion(SOLVER_STRING);
            String solverName = SmtLibSolverManager.getSolverName(SOLVER_STRING);
            if (solverManager.managesSolver(SOLVER_STRING)
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

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
    public void test(String filePath, String propPath, boolean safe, XstsConfigBuilder.Domain domain) throws Exception {
        initXstsTest(filePath, propPath, safe, domain);
        final Logger logger = new ConsoleLogger(Level.SUBSTEP);
        SolverManager.registerSolverManager(
                hu.bme.mit.theta.solver.z3legacy.Z3SolverManager.create());
        SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create());
        SolverManager.registerSolverManager(SmtLibSolverManager.create(SMTLIB_HOME, logger));
        SolverManager.registerSolverManager(JavaSMTSolverManager.create());

        final SolverFactory solverFactory;
        try {
            solverFactory = SolverManager.resolveSolverFactory(SOLVER_STRING);
        } catch (Exception e) {
            Assumptions.assumeFalse(true, e::toString);
            return;
        }

        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream(filePath), new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        try {
            final XstsConfig<?, ?, ?> configuration =
                    new XstsConfigBuilder(
                                    domain,
                                    XstsConfigBuilder.Refinement.SEQ_ITP,
                                    solverFactory,
                                    solverFactory)
                            .initPrec(XstsConfigBuilder.InitPrec.CTRL)
                            .optimizeStmts(XstsConfigBuilder.OptimizeStmts.ON)
                            .predSplit(XstsConfigBuilder.PredSplit.CONJUNCTS)
                            .maxEnum(250)
                            .autoExpl(XstsConfigBuilder.AutoExpl.NEWOPERANDS)
                            .logger(logger)
                            .build(xsts);
            final SafetyResult<?, ?> status = configuration.check();

            if (safe) {
                assertTrue(status.isSafe());
            } else {
                assertTrue(status.isUnsafe());
            }
        } finally {
            SolverManager.closeAll();
        }
    }

    public void initXstsTest(String filePath, String propPath, boolean safe, XstsConfigBuilder.Domain domain) {
        this.filePath = filePath;
        this.propPath = propPath;
        this.safe = safe;
        this.domain = domain;
    }
}
