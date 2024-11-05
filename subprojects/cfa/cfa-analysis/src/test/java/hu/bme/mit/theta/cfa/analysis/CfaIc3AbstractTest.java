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
package hu.bme.mit.theta.cfa.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprCegarChecker;
import hu.bme.mit.theta.analysis.algorithm.bounded.ReversedMonolithicExprKt;
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3SolverManager;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileInputStream;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.EXPL;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.PRED_BOOL;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.PRED_CART;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.BW_BIN_ITP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.NWT_IT_WP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.SEQ_ITP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.UCB;

@RunWith(value = Parameterized.class)
public class CfaIc3AbstractTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public boolean isSafe;

    @Parameterized.Parameters(name = "{index}: {0}, {1}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

//                {"src/test/resources/arithmetic-bool00.cfa", false},
//
//                {"src/test/resources/arithmetic-bool01.cfa", false},
//
//                {"src/test/resources/arithmetic-bool10.cfa", false},
//
//                {"src/test/resources/arithmetic-bool11.cfa", false},
//
//                {"src/test/resources/arithmetic-int.cfa", false},
//
//                {"src/test/resources/arithmetic-mod.cfa", true},
//
//                {"src/test/resources/arrays.cfa", false},
//
//                {"src/test/resources/arrayinit.cfa", false},
//
//                {"src/test/resources/arrays.cfa", false},

                {"src/test/resources/counter5_true.cfa", true},

                {"src/test/resources/ifelse.cfa", false},

                {"src/test/resources/locking.cfa", true},

        });
    }

    @Test
    public void test() throws Exception {
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if (OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            SolverManager.registerSolverManager(
                    SmtLibSolverManager.create(SmtLibSolverManager.HOME, NullLogger.getInstance()));
        }

        final SolverFactory solverFactory;
        try {
            solverFactory = SolverManager.resolveSolverFactory("Z3");
        } catch (Exception e) {
            Assume.assumeNoException(e);
            return;
        }

        try {
            CFA cfa = CfaDslManager.createCfa(new FileInputStream(filePath));
            final MonolithicExpr monolithicExpr = CfaToMonolithicExprKt.toMonolithicExpr(cfa);
            MonolithicExpr reverseMonolithicExpr = ReversedMonolithicExprKt.createReversed(monolithicExpr);

            var checker = new MonolithicExprCegarChecker<>(monolithicExpr,
                    mE -> new Ic3Checker<>(
                            mE,
                            true,
                            Z3LegacySolverFactory.getInstance(),
                            mE.getValToState()::invoke,
                            mE.getBiValToAction()::invoke,
                            false
                    ),
                    valuation -> CfaToMonolithicExprKt.valToState(cfa, valuation),
                    (v1, v2) -> CfaToMonolithicExprKt.valToAction(cfa, v1, v2),
                    new ConsoleLogger(Logger.Level.INFO),
                    Z3LegacySolverFactory.getInstance());
            Assert.assertEquals(isSafe, checker.check().isSafe());
        } finally {
            SolverManager.closeAll();
        }
    }


}
