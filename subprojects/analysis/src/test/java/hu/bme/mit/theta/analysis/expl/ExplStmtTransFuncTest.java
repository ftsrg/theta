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
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class ExplStmtTransFuncTest {
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();
	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	@Test
	public void testSimple() {
		final ExplStmtTransFunc transFunc = ExplStmtTransFunc.create(solver, 0);
		final ExplState sourceState = ExplState.top();
		final ExplPrec prec = ExplPrec.of(Collections.singleton(x));
		final List<Stmt> stmts = new ArrayList<>();
		stmts.add(Havoc(x));
		stmts.add(Assign(x, Int(0)));
		stmts.add(Assign(x, Add(x.getRef(), Int(1))));
		stmts.add(Assign(x, Add(x.getRef(), Int(1))));
		stmts.add(Assume(Leq(x.getRef(), Int(100))));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(sourceState, stmts, prec);

		Assert.assertEquals(1, succStates.size());
		final ExplState expectedState = ExplState.of(ImmutableValuation.builder().put(x, Int(2)).build());
		Assert.assertEquals(expectedState, Utils.singleElementOf(succStates));
	}

	@Test
	public void testBottom() {
		final ExplStmtTransFunc transFunc = ExplStmtTransFunc.create(solver, 0);
		final ExplState sourceState = ExplState.top();
		final ExplPrec prec = ExplPrec.of(Collections.singleton(x));
		final List<Stmt> stmts = new ArrayList<>();
		stmts.add(Havoc(x));
		stmts.add(Assume(Lt(Mul(x.getRef(), x.getRef()), Int(0))));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(sourceState, stmts, prec);

		Assert.assertEquals(1, succStates.size());
		final ExplState expectedState = ExplState.bottom();
		Assert.assertEquals(expectedState, Utils.singleElementOf(succStates));
	}

	@Test
	public void testComplex1() {
		final ExplStmtTransFunc transFunc = ExplStmtTransFunc.create(solver, 0);
		final ExplState sourceState = ExplState.top();
		final ExplPrec prec = ExplPrec.of(ImmutableSet.of(x, y));
		final List<Stmt> stmts = new ArrayList<>();
		stmts.add(Assign(x, Int(5)));
		stmts.add(Assume(Eq(x.getRef(), y.getRef())));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(sourceState, stmts, prec);

		Assert.assertEquals(1, succStates.size());
		final ExplState expectedState = ExplState
				.of(ImmutableValuation.builder().put(x, Int(5)).put(y, Int(5)).build());
		Assert.assertEquals(expectedState, Utils.singleElementOf(succStates));
	}

	@Test
	public void testComplex2() {
		final ExplStmtTransFunc transFunc = ExplStmtTransFunc.create(solver, 1);
		final ExplState sourceState = ExplState.top();
		final ExplPrec prec = ExplPrec.of(ImmutableSet.of(x, y));
		final List<Stmt> stmts = new ArrayList<>();
		stmts.add(Assign(x, Int(5)));
		stmts.add(Assume(Eq(x.getRef(), y.getRef())));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(sourceState, stmts, prec);

		Assert.assertEquals(1, succStates.size());
		final ExplState expectedState = ExplState
				.of(ImmutableValuation.builder().put(x, Int(5)).put(y, Int(5)).build());
		Assert.assertEquals(expectedState, Utils.singleElementOf(succStates));
	}

	@Test
	public void testComplex3() {
		final ExplState sourceState = ExplState.top();
		final ExplPrec prec = ExplPrec.of(Collections.singleton(x));
		final List<Stmt> stmts = new ArrayList<>();
		stmts.add(Assume(BoolExprs.And(Leq(Int(0), x.getRef()), Leq(x.getRef(), Int(2)))));

		final Map<Integer, Integer> solverCallsToExpectedStates = new HashMap<>();
		solverCallsToExpectedStates.put(1, 1);
		solverCallsToExpectedStates.put(2, 1);
		solverCallsToExpectedStates.put(3, 3);
		solverCallsToExpectedStates.put(4, 3);
		solverCallsToExpectedStates.put(0, 3);

		for (final Entry<Integer, Integer> entry : solverCallsToExpectedStates.entrySet()) {
			final ExplStmtTransFunc transFunc = ExplStmtTransFunc.create(solver, entry.getKey());
			final Collection<? extends ExplState> succStates = transFunc.getSuccStates(sourceState, stmts, prec);

			Assert.assertEquals(entry.getValue().intValue(), succStates.size());
		}

	}
}
