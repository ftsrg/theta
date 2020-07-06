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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;

import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class ExplInitFuncTest {
	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();

	@Test
	public void test1() {
		final ExplPrec prec = ExplPrec.of(ImmutableList.of(x));
		final ExplInitFunc initFunc = ExplInitFunc.create(solver, True());
		Assert.assertEquals(1, initFunc.getInitStates(prec).size());
	}

	@Test
	public void test2() {
		final ExplPrec prec = ExplPrec.of(ImmutableList.of(x, y));
		final ExplInitFunc initFunc = ExplInitFunc.create(solver,
				And(Leq(Int(0), x.getRef()), Leq(x.getRef(), Int(5))));
		Assert.assertEquals(6, initFunc.getInitStates(prec).size());
	}

	@Test
	public void test3() {
		final ExplPrec prec = ExplPrec.of(ImmutableList.of(x, y));
		final ExplInitFunc initFunc = ExplInitFunc.create(solver,
				And(Leq(Int(0), x.getRef()), Leq(x.getRef(), y.getRef()), Leq(y.getRef(), Int(3))));
		Assert.assertEquals(10, initFunc.getInitStates(prec).size());
	}

	@Test
	public void testBottom() {
		final ExplPrec prec = ExplPrec.of(ImmutableList.of(x, y));
		final ExplInitFunc initFunc = ExplInitFunc.create(solver,
				And(Leq(Int(5), x.getRef()), Leq(x.getRef(), y.getRef()), Leq(y.getRef(), Int(3))));
		final Collection<? extends ExplState> initStates = initFunc.getInitStates(prec);
		Assert.assertEquals(1, initStates.size());
		Assert.assertEquals(ExplState.bottom(), Utils.singleElementOf(initStates));
	}
}
