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
package hu.bme.mit.theta.solver.z3;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public final class Z3ModelTest {

    static {
        Z3SolverFactory.getInstance();
    }

    @Test
    public void test() {
        final Context context = new Context();
        final Solver solver = context.mkSimpleSolver();

        final BoolExpr a = context.mkBoolConst("a");
        final BoolExpr b = context.mkBoolConst("b");
        final BoolExpr expr = context.mkOr(a, b);

        solver.add(expr);
        solver.check();
        final Model model = solver.getModel();

        Assertions.assertTrue(model.getConstInterp(a).isTrue());
        Assertions.assertNull(model.getConstInterp(b));

        context.close();
    }

    @Test
    public void testFuncInterpEntriesKeepTheirArguments() {
        final Context context = new Context();
        final Solver solver = context.mkSimpleSolver();

        final FuncDecl<BoolSort> f =
                context.mkFuncDecl("f", new Sort[] {context.getIntSort()}, context.getBoolSort());
        solver.add((BoolExpr) f.apply(context.mkInt(1)));
        solver.add(context.mkNot((BoolExpr) f.apply(context.mkInt(2))));
        Assertions.assertEquals(Status.SATISFIABLE, solver.check());

        final BoolExpr body = InterpolationMetadata.interpretation(context, solver.getModel(), f);

        // f(1) and f(2) disagree, so a reconstruction that drops the entries' arguments is wrong.
        Assertions.assertTrue(holdsAt(context, body, 1));
        Assertions.assertFalse(holdsAt(context, body, 2));

        context.close();
    }

    /** Whether [body], read as the interpretation of a unary predicate, holds at [arg]. */
    private static boolean holdsAt(final Context context, final BoolExpr body, final int arg) {
        final Solver solver = context.mkSimpleSolver();
        solver.add(context.mkNot((BoolExpr) body.substituteVars(new Expr[] {context.mkInt(arg)})));
        return solver.check() == Status.UNSATISFIABLE;
    }
}
