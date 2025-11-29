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
package hu.bme.mit.theta.cfa.analysis;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.InvariantProof;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3legacy.Z3SolverManager;
import java.io.FileInputStream;
import java.util.Arrays;
import java.util.Collection;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.jupiter.api.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = Parameterized.class)
public class CfaMddCheckerTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public boolean isSafe;

    @Parameterized.Parameters(name = "{index}: {0}, {1}")
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"src/test/resources/arithmetic-bool00.cfa", false},
                    {"src/test/resources/arithmetic-bool01.cfa", false},
                    {"src/test/resources/arithmetic-bool10.cfa", false},
                    {"src/test/resources/arithmetic-bool11.cfa", false},
                    {"src/test/resources/arithmetic-mod.cfa", true},
                    {"src/test/resources/counter5_true.cfa", true},
                    {"src/test/resources/counter_bv_true.cfa", true},
                    {"src/test/resources/counter_bv_false.cfa", false},
                    {"src/test/resources/ifelse.cfa", false},
                });
    }

    @Test
    public void test() throws Exception {
        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

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

            final SafetyResult<InvariantProof, Trace<CfaState<ExplState>, CfaAction>> status;
            try (var solverPool = new SolverPool(solverFactory)) {
                final var checker =
                        new CfaPipelineChecker<>(
                                cfa,
                                monolithicExpr ->
                                        new MddChecker(monolithicExpr, solverPool, logger));
                status = checker.check(null);
            }

            Assert.assertEquals(isSafe, status.isSafe());
        } finally {
            SolverManager.closeAll();
        }
    }
}
