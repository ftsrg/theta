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
package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class ExprOrdLeqTest {

    private static final Expr<IntType> X = Var("x", Int()).getRef();
    public ExprState state1;
    public ExprState state2;
    public boolean leq;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {PredState.of(), PredState.of(), true},
                    {PredState.of(Geq(X, Int(0))), PredState.of(True()), true},
                    {PredState.of(False()), PredState.of(Leq(X, Int(1))), true},
                    {PredState.of(True()), PredState.of(Geq(X, Int(0))), false},
                    {PredState.of(Geq(X, Int(0))), PredState.of(False()), false}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testIsTop(ExprState state1, ExprState state2, boolean leq) {
        initExprOrdLeqTest(state1, state2, leq);
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        final PartialOrd<ExprState> ord = ExprOrd.create(solver);
        assertEquals(ord.isLeq(state1, state2), leq);
    }

    public void initExprOrdLeqTest(ExprState state1, ExprState state2, boolean leq) {
        this.state1 = state1;
        this.state2 = state2;
        this.leq = leq;
    }
}
