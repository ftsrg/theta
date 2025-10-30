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
package hu.bme.mit.theta.solver.eldarica;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assume.assumeFalse;
import static org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExpressionUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import java.util.Collection;
import java.util.function.Predicate;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

@RunWith(Parameterized.class)
public class EldaricaTransformerTest {

    @Parameter(0)
    public Expr<?> expr;

    private static Solver helperSolver = Z3SolverFactory.getInstance().createSolver();

    @Parameters(name = "expr: {0}")
    public static Collection<?> operations() {
        return ExpressionUtils.AllExpressions().values().stream()
                .map(object -> new Object[] {object})
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
    public void testRoundtripTransformer() {
        // Sanity check
        assertNotNull(expr);
        assumeFalse(hasType(expr, type -> type instanceof FpType || type instanceof RatType));
        assumeFalse(
                hasExpr(
                        expr,
                        expr ->
                                expr instanceof BvRotateLeftExpr
                                        || expr instanceof BvRotateRightExpr));

        final EldaricaSymbolTable javaSMTSymbolTable = new EldaricaSymbolTable();
        final EldaricaTransformationManager manager =
                new EldaricaTransformationManager(javaSMTSymbolTable);
        final EldaricaTermTransformer javaSMTTermTransformer =
                new EldaricaTermTransformer(javaSMTSymbolTable);

        final var expTerm = manager.toTerm(expr).asExpression();
        final Expr<?> expExpr;
        try {
            expExpr = javaSMTTermTransformer.toExpr(expTerm);
        } catch (Throwable t) {
            System.err.printf("Not able to transform: %s -> %s -> ?%n", expr, expTerm);
            throw t;
        }

        try {
            Assert.assertEquals(expTerm.toString(), expr, expExpr);
        } catch (AssertionError e) {
            System.err.printf("Not equal syntactically: %s -> %s -> %s%n", expr, expTerm, expExpr);
            try (final var wpp = new WithPushPop(helperSolver)) {
                helperSolver.add(Eq(expr, expExpr));
                Assert.assertTrue(
                        "(= %s %s) is unsat\n".formatted(expr, expExpr),
                        helperSolver.check().isSat());
            }
            try (final var wpp = new WithPushPop(helperSolver)) {
                helperSolver.add(Not(Eq(expr, expExpr)));
                Assert.assertTrue(
                        "(not (= %s %s)) is sat with model %s\n"
                                .formatted(
                                        expr,
                                        expExpr,
                                        helperSolver.check().isSat()
                                                ? helperSolver.getModel()
                                                : ""),
                        helperSolver.check().isUnsat());
            }
        }
    }
}
