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
package hu.bme.mit.theta.solver.z3;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.UserPropagatorBase;
import org.junit.Test;

import java.util.StringJoiner;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public final class Z3UserPropagatorTest {

    private static class OrderingPropagator extends UserPropagatorBase {

        private OrderingPropagator(Context context, Solver solver) {
            super(context, solver);
            registerCreated();
            registerDecide();
            registerEq();
            registerFinal();
            registerFixed();
        }

        @Override
        public void push() {
            System.out.println("push()");
            // no-op
        }

        @Override
        public void pop(int i) {
            System.out.println("pop(" + i + ")");
            // no-op
        }

        @Override
        public UserPropagatorBase fresh(Context context) {
            System.out.println("fresh()");
            final com.microsoft.z3.Solver z3Solver = context.mkSimpleSolver();
            return new OrderingPropagator(context, z3Solver);
        }

        @Override
        public void created(Expr<?> expr) {
            System.out.println("created(" + new StringJoiner(", ").add(expr.toString()) + ")");
            super.created(expr);
        }

        @Override
        public void eq(Expr<?> expr, Expr<?> expr1) {
            System.out.println("eq(" + new StringJoiner(", ").add(expr.toString()).add(expr1.toString()) + ")");
            super.eq(expr, expr1);
        }

        @Override
        public void decide(Expr<?> expr, int i, boolean b) {
            System.out.println("decide(" + new StringJoiner(", ").add(expr.toString()).add(Integer.toString(i)).add(Boolean.toString(b)) + ")");
            super.decide(expr, i, b);
        }

        @Override
        public void fin() {
            System.out.println("fin()");
            super.fin();
        }
    }

    @Test
    public void setup() {
        final com.microsoft.z3.Context z3Context = new com.microsoft.z3.Context();

        final com.microsoft.z3.Solver z3Solver = z3Context.mkSimpleSolver();

        final OrderingPropagator orderingPropagator = new OrderingPropagator(z3Context, z3Solver);

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager = new Z3TransformationManager(
                symbolTable, z3Context);

        final var x = transformationManager.toTerm(Const("x", Int()).getRef());
        final var y = transformationManager.toTerm(Const("y", Int()).getRef());

        final var propFunc = z3Context.mkPropagateFunction(z3Context.mkSymbol("order"), new Sort[]{z3Context.getIntSort(), z3Context.getIntSort()}, z3Context.getBoolSort());
        final var expr = propFunc.apply(x, y);

        orderingPropagator.add(x);
        orderingPropagator.add(y);

        z3Solver.add(expr);
        z3Solver.add(z3Context.mkEq(x, y));

        System.out.println(z3Solver.check());
        System.out.println(z3Solver.getModel());


    }

}
