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

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.tracegeneration.XstsTracegenBuilder;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.time.Duration;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import org.junit.jupiter.api.Test;

public class XstsTracegenTest {

    /**
     * The variables of the model are initialized only in their declarations and their guards have
     * infinitely many models when unconstrained, so ignoring the initializers makes trace
     * generation run forever instead of failing.
     */
    @Test
    public void testDeclarationInitializers() throws IOException {
        final XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream("src/test/resources/model/decl_init.xsts"),
                        new ByteArrayInputStream("prop { true }".getBytes()))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        final var config =
                new XstsTracegenBuilder(Z3LegacySolverFactory.getInstance(), true).build(xsts);
        final Collection<? extends ArgTrace<?, ?>> traces =
                assertTimeoutPreemptively(
                        Duration.ofSeconds(60),
                        () -> config.check().getSummary().getSourceTraces());

        final Map<Decl<?>, LitExpr<?>> expectedInit = new HashMap<>();
        for (VarDecl<?> var : xsts.getVars()) {
            expectedInit.put(var, Int(0));
        }
        assertFalse(traces.isEmpty());
        for (ArgTrace<?, ?> trace : traces) {
            final var initState = (XstsState<?>) trace.node(0).getState();
            assertEquals(expectedInit, ((ExplState) initState.getState()).toMap());
        }
    }
}
