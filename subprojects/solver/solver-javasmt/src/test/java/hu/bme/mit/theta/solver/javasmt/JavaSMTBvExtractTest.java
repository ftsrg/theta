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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.OsHelper.OperatingSystem;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import java.util.List;
import java.util.regex.Matcher;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

/** Solvers print the indices of an extract differently; each form must be read back. */
public class JavaSMTBvExtractTest {

    // MathSAT is not loaded here: its native library crashes the CI test JVM.
    @Test
    public void mathsatExtractIndices() {
        final Matcher match =
                JavaSMTTermTransformer.EXTRACT_INDICES.matcher("(`bvextract_6_3_8` x_0)");
        assertTrue(match.find());
        assertEquals("6", match.group(1));
        assertEquals("3", match.group(2));
    }

    @ParameterizedTest
    @EnumSource(
            value = Solvers.class,
            names = {"Z3", "CVC5"})
    public void extractRoundtrip(final Solvers solver) throws Exception {
        assumeTrue(
                solver == Solvers.Z3 || OsHelper.getOs() == OperatingSystem.LINUX,
                "native libraries of " + solver + " are only shipped for Linux");

        final Expr<BvType> x = Const("x", BvExprs.BvType(8)).getRef();
        final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
        final var config = Configuration.fromCmdLineArguments(new String[] {});
        try (final SolverContext context =
                SolverContextFactory.createSolverContext(
                        config,
                        BasicLogManager.create(config),
                        ShutdownManager.create().getNotifier(),
                        solver)) {
            final var exprTransformer = new JavaSMTTransformationManager(symbolTable, context);
            final var termTransformer = new JavaSMTTermTransformer(symbolTable, context);

            for (final BvExtractExpr extract :
                    List.of(
                            BvExtractExpr.of(x, Int(3), Int(7)),
                            BvExtractExpr.of(x, Int(0), Int(1)))) {
                assertEquals(extract, termTransformer.toExpr(exprTransformer.toTerm(extract)));
            }
        }
    }
}
