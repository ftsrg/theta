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
package hu.bme.mit.theta.solver.javasmt;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.utils.BvTestUtils;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import hu.bme.mit.theta.core.utils.IntTestUtils;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static org.junit.Assert.assertNotNull;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class JavaSMTTransformerTest {

    @Parameterized.Parameter(0)
    public Expr<?> expr;

    @Parameters(name = "expr: {0}")
    public static Collection<?> operations() {
        return Stream.of(
                BvTestUtils.BasicOperations().stream().map(o -> ((Object[])o)[2]),
                BvTestUtils.BitvectorOperations().stream().map(o -> ((Object[])o)[2]),
                BvTestUtils.RelationalOperations().stream().map(o -> ((Object[])o)[2]),
                FpTestUtils.GetOperations().map(o -> ((Object[])o)[2]),
                IntTestUtils.BasicOperations().stream().map(o -> ((Object[])o)[2]),

                BvTestUtils.BasicOperations().stream().map(o -> ((Object[])o)[1]),
                BvTestUtils.BitvectorOperations().stream().map(o -> ((Object[])o)[1]),
                BvTestUtils.RelationalOperations().stream().map(o -> ((Object[])o)[1]),
                FpTestUtils.GetOperations().map(o -> ((Object[])o)[1]),
                IntTestUtils.BasicOperations().stream().map(o -> ((Object[])o)[1])
        ).reduce(Stream::concat).get()
                .filter(JavaSMTTransformerTest::supported)
                .collect(Collectors.toSet());
    }

    private static boolean supported(Object o) {
        return !(o instanceof BvRotateLeftExpr) &&
                !(o instanceof BvRotateRightExpr) &&
                !(o instanceof FpToBvExpr) &&
                !(o instanceof FpFromBvExpr) &&
                !(o instanceof FpToFpExpr) &&
                !(o instanceof BvZExtExpr) &&
                !(o instanceof BvSExtExpr) &&
                !(o instanceof BvExtractExpr) &&
                !(o instanceof FpRemExpr) &&
                (!(o instanceof Expr<?>) || ((Expr<?>) o).getOps().stream().allMatch(JavaSMTTransformerTest::supported));
    }


    @Test
    public void testRoundtripTransformer() throws InvalidConfigurationException {
        // Sanity check
        assertNotNull(expr);

        final JavaSMTSymbolTable javaSMTSymbolTable = new JavaSMTSymbolTable();
        final var config = Configuration.fromCmdLineArguments(new String[]{});
        final var logger = BasicLogManager.create(config);
        final var shutdownManager = ShutdownManager.create();
        final SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdownManager.getNotifier(), Solvers.Z3);
        final JavaSMTTransformationManager javaSMTExprTransformer = new JavaSMTTransformationManager(javaSMTSymbolTable, context);
        final JavaSMTTermTransformer javaSMTTermTransformer = new JavaSMTTermTransformer(javaSMTSymbolTable, context);

        final var expTerm = javaSMTExprTransformer.toTerm(expr);
        final var expExpr = javaSMTTermTransformer.toExpr(expTerm);

        try {
            Assert.assertEquals(expr, expExpr);
        } catch (AssertionError e) {
            final var solver = JavaSMTSolverFactory.create(Solvers.Z3, new String[]{}).createSolver();
            solver.add(Eq(expr, expExpr));
            Assert.assertTrue(solver.check().isSat());
        }

    }
}
