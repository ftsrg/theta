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
package hu.bme.mit.theta.analysis.expl;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class ExplStatePredicateTest {

    private static final VarDecl<IntType> x = Var("x", Int());
    private final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
    public Expr<BoolType> expr;
    public ExplState state;
    public boolean expected;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        True(),
                        ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build()),
                        true
                    },
                    {
                        Leq(x.getRef(), Int(5)),
                        ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build()),
                        true
                    },
                    {
                        Leq(x.getRef(), Int(5)),
                        ExplState.of(ImmutableValuation.builder().put(x, Int(7)).build()),
                        false
                    },
                    {Geq(Mul(x.getRef(), x.getRef()), Int(0)), ExplState.top(), true},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(Expr<BoolType> expr, ExplState state, boolean expected) {
        initExplStatePredicateTest(expr, state, expected);
        assertEquals(expected, new ExplStatePredicate(expr, solver).test(state));
    }

    public void initExplStatePredicateTest(Expr<BoolType> expr, ExplState state, boolean expected) {
        this.expr = expr;
        this.state = state;
        this.expected = expected;
    }
}
