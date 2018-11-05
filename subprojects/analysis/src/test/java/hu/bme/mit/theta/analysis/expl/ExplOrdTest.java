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

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplOrdTest {

	private final VarDecl<IntType> X = Decls.Var("x", Int());
	private final VarDecl<IntType> Y = Decls.Var("y", Int());

	private final ExplOrd ord = ExplOrd.getInstance();

	private final ExplState st = ExplState.top();
	private final ExplState s1 = ExplState.of(ImmutableValuation.builder().put(X, Int(1)).build());
	private final ExplState s2 = ExplState.of(ImmutableValuation.builder().put(X, Int(2)).build());
	private final ExplState s3 = ExplState.of(ImmutableValuation.builder().put(Y, Int(1)).build());
	private final ExplState s4 = ExplState.of(ImmutableValuation.builder().put(X, Int(1)).put(Y, Int(1)).build());
	private final ExplState sb = ExplState.bottom();

	@Test
	public void testBottom() {
		Assert.assertFalse(st.isBottom());
		Assert.assertFalse(s1.isBottom());
		Assert.assertFalse(s2.isBottom());
		Assert.assertFalse(s3.isBottom());
		Assert.assertFalse(s4.isBottom());
		Assert.assertTrue(sb.isBottom());
	}

	@Test
	public void testLeq() {
		Assert.assertTrue(ord.isLeq(st, st));
		Assert.assertTrue(ord.isLeq(s1, st));
		Assert.assertTrue(ord.isLeq(s2, st));
		Assert.assertTrue(ord.isLeq(s3, st));
		Assert.assertTrue(ord.isLeq(s4, st));
		Assert.assertTrue(ord.isLeq(sb, st));

		Assert.assertFalse(ord.isLeq(st, s1));
		Assert.assertTrue(ord.isLeq(s1, s1));
		Assert.assertFalse(ord.isLeq(s2, s1));
		Assert.assertFalse(ord.isLeq(s3, s1));
		Assert.assertTrue(ord.isLeq(s4, s1));
		Assert.assertTrue(ord.isLeq(sb, s1));

		Assert.assertFalse(ord.isLeq(st, s2));
		Assert.assertFalse(ord.isLeq(s1, s2));
		Assert.assertTrue(ord.isLeq(s2, s2));
		Assert.assertFalse(ord.isLeq(s3, s2));
		Assert.assertFalse(ord.isLeq(s4, s2));
		Assert.assertTrue(ord.isLeq(sb, s2));

		Assert.assertFalse(ord.isLeq(st, s3));
		Assert.assertFalse(ord.isLeq(s1, s3));
		Assert.assertFalse(ord.isLeq(s2, s3));
		Assert.assertTrue(ord.isLeq(s3, s3));
		Assert.assertTrue(ord.isLeq(s4, s3));
		Assert.assertTrue(ord.isLeq(sb, s3));

		Assert.assertFalse(ord.isLeq(st, s4));
		Assert.assertFalse(ord.isLeq(s1, s4));
		Assert.assertFalse(ord.isLeq(s2, s4));
		Assert.assertFalse(ord.isLeq(s3, s4));
		Assert.assertTrue(ord.isLeq(s4, s4));
		Assert.assertTrue(ord.isLeq(sb, s4));

		Assert.assertFalse(ord.isLeq(st, sb));
		Assert.assertFalse(ord.isLeq(s1, sb));
		Assert.assertFalse(ord.isLeq(s2, sb));
		Assert.assertFalse(ord.isLeq(s3, sb));
		Assert.assertFalse(ord.isLeq(s4, sb));
		Assert.assertTrue(ord.isLeq(sb, sb));
	}
}
