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
package hu.bme.mit.theta.vmt.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedCheckerBuilderKt;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.vmt.VmtModel;
import hu.bme.mit.theta.vmt.VmtParser;
import hu.bme.mit.theta.vmt.VmtProperty;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaProverPool;
import hu.bme.mit.theta.vmt.analysis.mdd.VmtMddChecker;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

/** Cross-checks the VMT MDD checker against Theta's checkers on the converted models. */
public class VmtToMonolithicExprTest {

    private SolverContext context;
    private FormulaProverPool pool;

    @BeforeEach
    public void setUp() throws Exception {
        context = SolverContextFactory.createSolverContext(Solvers.Z3);
        pool = new FormulaProverPool(context);
    }

    @AfterEach
    public void tearDown() {
        pool.close();
        context.close();
    }

    public static Stream<Arguments> data() throws Exception {
        final List<Arguments> args = new ArrayList<>();
        for (String file :
                List.of(
                        "counter.vmt",
                        "bvinput.vmt",
                        "events.vmt",
                        "nondet.vmt",
                        "negated-identity.vmt",
                        "uf-bool.vmt",
                        "uf-bitvector.vmt")) {
            try (SolverContext c = SolverContextFactory.createSolverContext(Solvers.Z3)) {
                final VmtModel model =
                        VmtParser.parse(
                                Path.of("src/test/resources/" + file), c.getFormulaManager());
                for (VmtProperty p : model.getInvariantProperties())
                    args.add(Arguments.of(file, p.index()));
            }
        }
        return args.stream();
    }

    @ParameterizedTest(name = "{0} property {1}")
    @MethodSource("data")
    public void test(String file, int propertyIndex) throws Exception {
        final VmtModel model =
                VmtParser.parse(Path.of("src/test/resources/" + file), context.getFormulaManager());
        final VmtProperty property =
                model.getInvariantProperties().stream()
                        .filter(p -> p.index() == propertyIndex)
                        .findFirst()
                        .orElseThrow();
        final boolean expected =
                new VmtMddChecker(model, pool, NullLogger.getInstance(), property)
                        .check(UnitPrec.getInstance())
                        .isSafe();

        final var monolithic =
                new VmtToMonolithicExpr(model, context, property).getMonolithicExpr();
        final var factory = Z3LegacySolverFactory.getInstance();
        final var kind =
                BoundedCheckerBuilderKt.buildKIND(
                                monolithic,
                                factory.createSolver(),
                                factory.createSolver(),
                                NullLogger.getInstance(),
                                k -> k > 40)
                        .check();
        assertFalse(!kind.isSafe() && !kind.isUnsafe(), "k-induction gave up");
        assertEquals(expected, kind.isSafe(), "k-induction");

        // an input becomes a variable with a free next-state value, which the expression-based
        // MDD checker does not handle (it reports safe), so it is only compared without inputs
        if (!model.getInputVars().isEmpty()) return;
        final var mdd =
                new MddChecker(
                                monolithic,
                                new SolverPool(factory),
                                NullLogger.getInstance(),
                                IterationStrategy.GSAT)
                        .check(null);
        assertEquals(expected, mdd.isSafe(), "expression-based MDD checker");
    }
}
