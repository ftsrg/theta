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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Optional;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplStateTest {

	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	@Test
	public void testInstances() {
		final ExplState t1 = ExplState.top();
		final ExplState t2 = ExplState.top();
		final ExplState t3 = ExplState.of(ImmutableValuation.empty());
		final ExplState s1 = ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build());
		final ExplState s2 = ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build());
		final ExplState b = ExplState.bottom();

		Assert.assertSame(t1, t2);
		Assert.assertSame(t1, t3);
		Assert.assertSame(t2, t3);

		Assert.assertNotSame(s1, t1);
		Assert.assertEquals(s1, s2);

		Assert.assertNotEquals(t1, b);
		Assert.assertNotEquals(t2, b);
	}

	@Test
	public void testEval() {
		final ExplState s1 = ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build());

		Assert.assertEquals(Optional.of(Int(1)), s1.eval(x));
		Assert.assertEquals(Optional.empty(), s1.eval(y));
	}

	@Test
	public void testToExpr() {
		Assert.assertEquals(True(), ExplState.top().toExpr());
		Assert.assertEquals(False(), ExplState.bottom().toExpr());
		Assert.assertEquals(And(Eq(x.getRef(), Int(1)), Eq(y.getRef(), Int(2))),
				ExplState.of(ImmutableValuation.builder().put(x, Int(1)).put(y, Int(2)).build()).toExpr());
	}
}
