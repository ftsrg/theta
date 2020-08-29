/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

@RunWith(Parameterized.class)
public class ExplStatePredicateTest {

	private static final VarDecl<IntType> x = Var("x", Int());
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();

	@Parameter(value = 0)
	public Expr<BoolType> expr;

	@Parameter(value = 1)
	public ExplState state;

	@Parameter(value = 2)
	public boolean expected;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{True(), ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build()), true},

				{Leq(x.getRef(), Int(5)), ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build()), true},

				{Leq(x.getRef(), Int(5)), ExplState.of(ImmutableValuation.builder().put(x, Int(7)).build()), false},

				{Geq(Mul(x.getRef(), x.getRef()), Int(0)), ExplState.top(), true},

		});
	}

	@Test
	public void test() {
		assertEquals(expected, new ExplStatePredicate(expr, solver).test(state));
	}
}
