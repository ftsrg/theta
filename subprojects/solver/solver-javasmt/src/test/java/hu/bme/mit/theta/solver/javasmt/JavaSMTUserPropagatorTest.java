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

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Test;

public class JavaSMTUserPropagatorTest {

    @Test
    public void testUserPropagatorBool() throws Exception {
        TestKnownValuePropagator testPropagator = new TestKnownValuePropagator();

        try (final var solver =
                JavaSMTSolverFactory.create(Z3, new String[] {})
                        .createSolverWithPropagators(testPropagator)) {
            final var c1 = Const("x", Bool());
            final var c2 = Const("y", Bool());
            final var c3 = Const("z", Bool());
            final var expr1 = Or(c1.getRef(), c2.getRef(), c3.getRef());

            testPropagator.registerExpression(c1.getRef(), false);
            testPropagator.registerExpression(c2.getRef(), false);

            solver.add(expr1);

            solver.check();
            assertTrue("Should be SAT", solver.getStatus().isSat());
        }
    }

    @Test
    public void testUserPropagatorFunc() throws Exception {
        TestConsequencePropagator testPropagator = new TestConsequencePropagator();

        try (final var solver =
                JavaSMTSolverFactory.create(Z3, new String[] {})
                        .createSolverWithPropagators(testPropagator)) {
            final var c1 = Const("x", Int());
            final var c2 = Const("y", Int());
            final var c3 = Const("z", Int());

            final var sortFuncType = FuncType.of(Int(), FuncType.of(Int(), Bool()));
            final var sortFunc = Const("sort", sortFuncType);

            final var expr1 = App(App(sortFunc.getRef(), c1.getRef()), c2.getRef());
            final var expr2 = App(App(sortFunc.getRef(), c2.getRef()), c3.getRef());

            solver.add(expr1);
            solver.add(expr2);
            solver.add(Eq(c1.getRef(), Int(0)));
            solver.add(Eq(c3.getRef(), Int(2)));

            testPropagator.registerExpression(expr1);
            testPropagator.registerExpression(expr2);

            solver.check();
            assertTrue("Should be SAT", solver.getStatus().isSat());

            final var model = solver.getModel();
            assertEquals(
                    "Should only be one.",
                    BigInteger.ONE,
                    ((IntLitExpr) model.eval(c2).get()).getValue());

            solver.add(Not(Eq(c2.getRef(), Int(1))));
            solver.check();
            assertTrue("Should be UNSAT", solver.getStatus().isUnsat());
        }
    }

    private static class TestConsequencePropagator extends JavaSMTUserPropagator {
        @Override
        public void onKnownValue(Expr<BoolType> expr, boolean value) {
            System.err.printf("%s := %s\n", expr, value);
            FuncAppExpr<?, ?> appOuter = (FuncAppExpr<?, ?>) expr;
            FuncAppExpr<?, ?> appInner = (FuncAppExpr<?, ?>) appOuter.getFunc();

            final var consequence =
                    Lt((Expr<IntType>) appInner.getParam(), (Expr<IntType>) appOuter.getParam());

            if (value) {
                System.err.printf("Consequence: %s\n", consequence);
                propagateConsequence(List.of(expr), consequence);
            } else {
                System.err.printf("Consequence: %s\n", Not(consequence));
                propagateConsequence(List.of(expr), Not(consequence));
            }
        }
    }

    private static class TestKnownValuePropagator extends JavaSMTUserPropagator {

        private final Map<Expr<BoolType>, Boolean> setExpressions = new LinkedHashMap<>();

        @Override
        public void onKnownValue(Expr<BoolType> expr, boolean value) {
            System.err.printf("%s := %s\n", expr, value);
            if (setExpressions.containsKey(expr) && value != setExpressions.get(expr)) {
                propagateConflict(List.of(expr));
            }
        }

        public void registerExpression(Expr<BoolType> expr, boolean value) {
            setExpressions.put(expr, value);
            this.registerExpression(expr);
        }
    }
}
