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
package hu.bme.mit.theta.xta.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgChecker;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfig;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfigFactory;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.Collection;
import java.util.List;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class CombinedLazyCegarXtaCheckerTest {

    public String modelPath;
    public String propPath;
    public ClockStrategy clockStrategy;
    public Boolean safety;

    private CombinedLazyCegarXtaCheckerConfig config;

    public static Collection<Object[]> data() {
        return List.<Object[]>of(
                new Object[] {"/model/AndOr.xta", "/property/AndOr.prop", null, true},
                // Extremely long
                // new Object[]{"/model/bangOlufsen.xta", "/property/bangOlufsen.prop", null, true},
                new Object[] {
                    "/model/fischer-2-32-64.xta", "/property/fischer-2-32-64.prop", null, true
                },
                new Object[] {"/model/mytest.xta", "/property/mytest.prop", null, true},
                new Object[] {
                    "/model/lazy-pruning-example.xta", "/property/p-errorloc.prop", null, true
                },
                new Object[] {
                    "/model/lazy-pruning-example-2.xta", "/property/p-errorloc.prop", null, true
                });
    }

    public void initialize() throws IOException {
        final InputStream inputStream =
                new SequenceInputStream(
                        getClass().getResourceAsStream(modelPath),
                        getClass().getResourceAsStream(propPath));
        final XtaSystem system = XtaDslManager.createSystem(inputStream);
        config =
                CombinedLazyCegarXtaCheckerConfigFactory.create(
                                system,
                                new ConsoleLogger(Logger.Level.MAINSTEP),
                                Z3LegacySolverFactory.getInstance())
                        .build();
    }

    @MethodSource("data")
    @ParameterizedTest(name = "model: {0}, prop: {1}, clocks: {2}, safety: {3}")
    public void test(String modelPath, String propPath, ClockStrategy clockStrategy, Boolean safety)
            throws IOException {
        initCombinedLazyCegarXtaCheckerTest(modelPath, propPath, clockStrategy, safety);

        // Act
        final SafetyResult<
                        ? extends ARG<? extends XtaState<?>, XtaAction>,
                        ? extends Trace<? extends XtaState<?>, XtaAction>>
                status = config.check();

        // Assert
        assertEquals(safety, status.isSafe());
        final ArgChecker argChecker =
                ArgChecker.create(Z3LegacySolverFactory.getInstance().createSolver());
        final boolean argCheckResult = argChecker.isWellLabeled(status.getProof());
        assertTrue(argCheckResult);
    }

    public void initCombinedLazyCegarXtaCheckerTest(
            String modelPath, String propPath, ClockStrategy clockStrategy, Boolean safety)
            throws IOException {
        this.modelPath = modelPath;
        this.propPath = propPath;
        this.clockStrategy = clockStrategy;
        this.safety = safety;
        this.initialize();
    }
}
