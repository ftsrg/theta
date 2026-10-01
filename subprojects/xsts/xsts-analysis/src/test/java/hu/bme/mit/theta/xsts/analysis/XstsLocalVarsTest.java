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
package hu.bme.mit.theta.xsts.analysis;

import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsStateSequence;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsTraceConcretizerUtil;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import org.junit.jupiter.api.Test;

/** Distinct local variables that share a name (with each other or with a global, #193). */
public class XstsLocalVarsTest {

    private static final String SAME_NAME = "localvars_same_name";
    private static final String SHADOW = "localvars_shadow";

    private static XSTS load(final String name) throws IOException {
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream("src/test/resources/model/" + name + ".xsts"),
                        new FileInputStream("src/test/resources/property/" + name + ".prop"))) {
            return XstsDslManager.createXsts(inputStream);
        }
    }

    private static SafetyResult<?, ?> checkHorn(final XSTS xsts) {
        return new HornChecker(
                        XstsToRelationsKt.toRelations(xsts),
                        Z3SolverFactory.getInstance(),
                        NullLogger.getInstance())
                .check();
    }

    @Test
    public void chcKeepsSameNameLocalsApart() throws IOException {
        assertTrue(checkHorn(load(SAME_NAME)).isUnsafe());
    }

    @Test
    public void chcKeepsLocalApartFromShadowedGlobal() throws IOException {
        assertTrue(checkHorn(load(SHADOW)).isUnsafe());
    }

    @Test
    @SuppressWarnings("unchecked")
    public void concretizedTraceHasOnlyStateVars() throws IOException {
        final XSTS xsts = load(SAME_NAME);
        final SolverFactory solverFactory = Z3LegacySolverFactory.getInstance();
        final SafetyResult<?, ?> status =
                new XstsConfigBuilder(
                                XstsConfigBuilder.Domain.EXPL,
                                XstsConfigBuilder.Refinement.SEQ_ITP,
                                solverFactory,
                                solverFactory)
                        .build(xsts)
                        .check();
        assertTrue(status.isUnsafe());

        final XstsStateSequence concrete =
                XstsTraceConcretizerUtil.concretize(
                        (Trace<XstsState<?>, XstsAction>) status.asUnsafe().getCex(),
                        solverFactory,
                        xsts);
        for (final XstsState<ExplState> state : concrete.getStates()) {
            assertTrue(
                    xsts.getStateVars().containsAll(state.getState().getDecls()),
                    () -> "Non-state variable in " + state);
        }
    }
}
