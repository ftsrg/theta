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
package hu.bme.mit.theta.solver.javasmt;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.OsHelper.OperatingSystem;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExpressionUtils;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

import java.util.Collection;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assume.assumeFalse;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class JavaSMTTransformerTest {

    @Parameter(0)
    public Expr<?> expr;

    @Parameter(1)
    public Solvers solver;

    @Parameters(name = "expr: {0}, solver: {1}")
    public static Collection<?> operations() {
        final Set<Solvers> solvers;
        if (OsHelper.getOs().equals(OperatingSystem.LINUX)) {
            solvers = Set.of(Solvers.Z3, Solvers.SMTINTERPOL, Solvers.CVC5, Solvers.PRINCESS);
        } else {
            solvers = Set.of(Solvers.Z3, Solvers.SMTINTERPOL, Solvers.PRINCESS);
        }

        return Sets.cartesianProduct(
                        ExpressionUtils.AllExpressions().values().stream()
                                .collect(Collectors.toSet()),
                        solvers)
                .stream()
                .map(objects -> new Object[] {objects.get(0), objects.get(1)})
                .toList();
    }

    private static boolean hasType(Expr<?> expr, Predicate<Type> pred) {
        if (pred.test(expr.getType())) return true;
        return expr.getOps().stream().anyMatch((op) -> hasType(op, pred));
    }

    private static boolean hasExpr(Expr<?> expr, Predicate<Expr<?>> pred) {
        if (pred.test(expr)) return true;
        return expr.getOps().stream().anyMatch((op) -> hasExpr(op, pred));
    }

    @Test
    public void testRoundtripTransformer() throws Exception {
        // Sanity check
        assertNotNull(expr);
        assumeFalse(
                solver == Solvers.CVC5
                        && hasType(
                                expr,
                                type ->
                                        type instanceof FpType
                                                && !Set.of(32, 64)
                                                        .contains(
                                                                ((FpType) type).getSignificand()
                                                                        + ((FpType) type)
                                                                                .getExponent())));
        assumeFalse(
                solver == Solvers.PRINCESS
                        && hasType(
                                expr, type -> type instanceof FpType || type instanceof RatType));
        assumeFalse(
                solver == Solvers.SMTINTERPOL
                        && (hasType(expr, type -> type instanceof BvType || type instanceof FpType)
                                || expr instanceof QuantifiedExpr));
        assumeFalse(
                solver == Solvers.SMTINTERPOL
                        && (hasType(expr, type -> type instanceof BvType || type instanceof FpType)
                                || expr instanceof QuantifiedExpr));
        assumeFalse(
                (solver == Solvers.SMTINTERPOL || solver == Solvers.PRINCESS)
                        && hasExpr(
                                expr,
                                e ->
                                        e instanceof ArrayInitExpr<?, ?>
                                                || e instanceof ArrayLitExpr<?, ?>));

        final JavaSMTSymbolTable javaSMTSymbolTable = new JavaSMTSymbolTable();
        final var config = Configuration.fromCmdLineArguments(new String[] {});
        final var logger = BasicLogManager.create(config);
        final var shutdownManager = ShutdownManager.create();
        try (final SolverContext context =
                SolverContextFactory.createSolverContext(
                        config, logger, shutdownManager.getNotifier(), Solvers.Z3)) {
            final JavaSMTTransformationManager javaSMTExprTransformer =
                    new JavaSMTTransformationManager(javaSMTSymbolTable, context);
            final JavaSMTTermTransformer javaSMTTermTransformer =
                    new JavaSMTTermTransformer(javaSMTSymbolTable, context);

            final var expTerm = javaSMTExprTransformer.toTerm(expr);
            final var expExpr = javaSMTTermTransformer.toExpr(expTerm);

            try {
                System.err.println(expr);
                System.err.println(expExpr);
                Assert.assertEquals(expr, expExpr);
            } catch (AssertionError e) {
                if (hasType(expr, type -> type instanceof FuncType<?, ?>)) {
                    throw e; // for functions, we don't want the solver to step in
                }
                try (final var solver =
                        JavaSMTSolverFactory.create(this.solver, new String[] {}).createSolver()) {
                    BiFunction<Expr, Expr, Expr<BoolType>> eq =
                            expr.getType() instanceof FpType
                                    ? FpExprs::FpAssign
                                    : AbstractExprs::Eq;

                    solver.push();
                    solver.add(eq.apply(expr, expExpr));
                    Assert.assertTrue(
                            "(= %s %s) is unsat\n".formatted(expr, expExpr),
                            solver.check().isSat());
                    solver.pop();
                    solver.push();
                    solver.add(Not(eq.apply(expr, expExpr)));
                    Assert.assertTrue(
                            "(not (= %s %s)) is sat with model %s\n"
                                    .formatted(
                                            expr,
                                            expExpr,
                                            solver.check().isSat() ? solver.getModel() : ""),
                            solver.check().isUnsat());
                    solver.pop();
                }
            }
        }
    }
}
