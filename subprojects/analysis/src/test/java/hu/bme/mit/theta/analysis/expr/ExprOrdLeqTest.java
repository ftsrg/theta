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
package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

@RunWith(Parameterized.class)
public final class ExprOrdLeqTest {

	private static final Expr<IntType> X = Var("x", Int()).getRef();

	@Parameter(value = 0)
	public ExprState state1;

	@Parameter(value = 1)
	public ExprState state2;

	@Parameter(value = 2)
	public boolean leq;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{PredState.of(), PredState.of(), true},

				{PredState.of(Geq(X, Int(0))), PredState.of(True()), true},

				{PredState.of(False()), PredState.of(Leq(X, Int(1))), true},

				{PredState.of(True()), PredState.of(Geq(X, Int(0))), false},

				{PredState.of(Geq(X, Int(0))), PredState.of(False()), false}

		});
	}

	@Test
	public void testIsTop() {
		final Solver solver = Z3SolverFactory.getInstance().createSolver();
		final PartialOrd<ExprState> ord = ExprOrd.create(solver);
		assertEquals(ord.isLeq(state1, state2), leq);
	}

}
