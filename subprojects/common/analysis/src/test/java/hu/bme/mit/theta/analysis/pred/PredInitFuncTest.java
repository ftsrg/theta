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
package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class PredInitFuncTest {

	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();
	private final PredAbstractor predAbstractor = PredAbstractors.booleanSplitAbstractor(solver);

	@Test
	public void test1() {
		// true -> (x>=0, y>=0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Geq(x.getRef(), Int(0)), Geq(y.getRef(), Int(0))));
		final PredInitFunc initFunc = PredInitFunc.create(predAbstractor, True());
		Assert.assertEquals(4, initFunc.getInitStates(prec).size());
	}

	@Test
	public void test2() {
		// (x>=0) -> (x>=0, y>=0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Geq(x.getRef(), Int(0)), Geq(y.getRef(), Int(0))));
		final PredInitFunc initFunc = PredInitFunc.create(predAbstractor, Geq(x.getRef(), Int(0)));
		Assert.assertEquals(2, initFunc.getInitStates(prec).size());
	}

	@Test
	public void test3() {
		// (x>=1) -> (x>=0, y>=0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Geq(x.getRef(), Int(0)), Geq(y.getRef(), Int(0))));
		final PredInitFunc initFunc = PredInitFunc.create(predAbstractor, Geq(x.getRef(), Int(1)));
		Assert.assertEquals(2, initFunc.getInitStates(prec).size());
	}

	@Test
	public void test4() {
		// true -> (x>0, x<0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Gt(x.getRef(), Int(0)), Lt(x.getRef(), Int(0))));
		final PredInitFunc initFunc = PredInitFunc.create(predAbstractor, True());
		Assert.assertEquals(3, initFunc.getInitStates(prec).size());
	}

	@Test
	public void testBottom() {
		// (x<0) and (x>0) -> (x>0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Gt(x.getRef(), Int(0))));
		final PredInitFunc initFunc = PredInitFunc.create(predAbstractor,
				And(Gt(x.getRef(), Int(0)), Lt(x.getRef(), Int(0))));
		final Collection<? extends PredState> initStates = initFunc.getInitStates(prec);
		Assert.assertEquals(1, initStates.size());
		Assert.assertEquals(PredState.bottom(), Utils.singleElementOf(initStates));
	}
}
