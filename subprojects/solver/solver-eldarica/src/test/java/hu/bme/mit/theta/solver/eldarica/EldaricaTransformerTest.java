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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

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
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class EldaricaTransformerTest {
    public Expr<?> expr;

    private static Solver helperSolver = Z3SolverFactory.getInstance().createSolver();

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

    @MethodSource("operations")
    @ParameterizedTest(name = "expr: {0}")
    public void testRoundtripTransformer(Expr<?> expr) {
        initEldaricaTransformerTest(expr);
        // Sanity check
        assertNotNull(expr);
        assumeFalse(hasType(expr, type -> type instanceof FpType || type instanceof RatType));
        assumeFalse(
                hasExpr(
                        expr,
                        e -> e instanceof BvRotateLeftExpr || e instanceof BvRotateRightExpr));

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
            Assertions.assertEquals(expr, expExpr, expTerm.toString());
        } catch (AssertionError e) {
            System.err.printf("Not equal syntactically: %s -> %s -> %s%n", expr, expTerm, expExpr);
            try (final var wpp = new WithPushPop(helperSolver)) {
                helperSolver.add(Eq(expr, expExpr));
                Assertions.assertTrue(
                        helperSolver.check().isSat(),
                        "(= %s %s) is unsat\n".formatted(expr, expExpr));
            }
            try (final var wpp = new WithPushPop(helperSolver)) {
                helperSolver.add(Not(Eq(expr, expExpr)));
                Assertions.assertTrue(
                        helperSolver.check().isUnsat(),
                        "(not (= %s %s)) is sat with model %s\n"
                                .formatted(
                                        expr,
                                        expExpr,
                                        helperSolver.check().isSat()
                                                ? helperSolver.getModel()
                                                : ""));
            }
        }
    }

    public void initEldaricaTransformerTest(Expr<?> expr) {
        this.expr = expr;
    }
}
