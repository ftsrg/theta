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
package hu.bme.mit.theta.solver.z3legacy;

import com.microsoft.z3legacy.BoolExpr;
import com.microsoft.z3legacy.Context;
import com.microsoft.z3legacy.Model;
import com.microsoft.z3legacy.Solver;
import org.junit.Assert;
import org.junit.Test;

public final class Z3ModelTest {

    static {
        Z3LegacySolverFactory.getInstance();
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

        Assert.assertTrue(model.getConstInterp(a).isTrue());
        Assert.assertNull(model.getConstInterp(b));

        context.close();
    }
}
