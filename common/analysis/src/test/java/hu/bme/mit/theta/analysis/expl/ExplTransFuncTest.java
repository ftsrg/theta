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
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class ExplTransFuncTest {
	private final VarDecl<IntType> x = Var("x", Int());
	private final ExplPrec prec = ExplPrec.of(ImmutableList.of(x));
	private final ExplState state = ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build());

	ExplTransFunc transFunc = ExplTransFunc.create(Z3SolverFactory.getInstance().createSolver());

	@Test
	public void testNormal() {
		final ExprAction action = mock(ExprAction.class);
		doReturn(Eq(Prime(x.getRef()), Add(x.getRef(), Int(1)))).when(action).toExpr();
		when(action.nextIndexing()).thenReturn(VarIndexing.all(1));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(state, action, prec);
		Assert.assertEquals(1, succStates.size());
		Assert.assertEquals(ExplState.of(ImmutableValuation.builder().put(x, Int(2)).build()),
				succStates.iterator().next());
	}

	@Test
	public void testBottom() {
		final ExprAction action = mock(ExprAction.class);
		doReturn(Eq(x.getRef(), Int(2))).when(action).toExpr();
		when(action.nextIndexing()).thenReturn(VarIndexing.all(1));

		final Collection<? extends ExplState> succStates = transFunc.getSuccStates(state, action, prec);
		Assert.assertEquals(1, succStates.size());
		Assert.assertEquals(ExplState.bottom(), Utils.singleElementOf(succStates));
	}
}
