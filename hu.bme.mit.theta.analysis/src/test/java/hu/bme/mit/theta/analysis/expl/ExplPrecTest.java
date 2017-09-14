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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplPrecTest {
	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	@Test
	public void testInstances() {
		final ExplPrec p1 = ExplPrec.create();
		final ExplPrec p2 = ExplPrec.create();
		final ExplPrec p3 = ExplPrec.create(Collections.emptySet());
		final ExplPrec p4 = ExplPrec.create(Collections.singleton(x));

		Assert.assertTrue(p1 == p2);
		Assert.assertTrue(p1 == p3);
		Assert.assertTrue(p1 != p4);
		Assert.assertTrue(p2 == p3);
		Assert.assertTrue(p2 != p4);
		Assert.assertTrue(p3 != p4);
	}

	@Test
	public void testMapping() {
		final ExplPrec prec = ExplPrec.create(Collections.singleton(x));
		final ExplState s1 = prec.createState(BasicValuation.builder().put(x, Int(1)).put(y, Int(2)).build());
		final ExplState s2 = prec.createState(BasicValuation.builder().put(y, Int(2)).build());

		Assert.assertEquals(1, s1.getDecls().size());
		Assert.assertEquals(Int(1), s1.eval(x).get());
		Assert.assertEquals(0, s2.getDecls().size());
	}

	@Test
	public void testRefinement() {
		final ExplPrec px = ExplPrec.create(Collections.singleton(x));
		final ExplPrec py = ExplPrec.create(Collections.singleton(y));
		final ExplPrec pxy = ExplPrec.create(ImmutableSet.of(x, y));

		final ExplPrec r1 = px.join(px);
		final ExplPrec r2 = px.join(py);
		final ExplPrec r3 = px.join(pxy);

		Assert.assertTrue(r1 == px);
		Assert.assertTrue(r2 != px);
		Assert.assertTrue(r3 == pxy);
	}

	@Test
	public void testEquals() {
		final ExplPrec p1 = ExplPrec.create();
		final ExplPrec p2 = ExplPrec.create();
		final ExplPrec p3 = ExplPrec.create(Collections.emptySet());
		final ExplPrec p4 = ExplPrec.create(Collections.singleton(x));
		final ExplPrec p5 = ExplPrec.create(Collections.singleton(x));
		final ExplPrec p6 = ExplPrec.create(ImmutableSet.of(x, y));
		final ExplPrec p7 = ExplPrec.create(ImmutableSet.of(x, y));

		Assert.assertEquals(p1, p2);
		Assert.assertEquals(p1, p3);
		Assert.assertEquals(p2, p3);
		Assert.assertEquals(p4, p5);
		Assert.assertEquals(p6, p7);

		Assert.assertNotEquals(p1, p4);
		Assert.assertNotEquals(p5, p7);
	}
}
