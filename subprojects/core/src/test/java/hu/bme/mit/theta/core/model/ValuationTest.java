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
package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ValuationTest {
	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());
	private final ConstDecl<IntType> cc = Const("c", Int());

	@Test
	public void testNullary() {
		final Valuation val = ImmutableValuation.empty();
		Assert.assertEquals(val.toExpr(), True());
	}

	@Test
	public void testUnary() {
		final Valuation val = ImmutableValuation.builder().put(ca, Int(5)).build();
		Assert.assertEquals(val.toExpr(), Eq(ca.getRef(), Int(5)));
	}

	@Test
	public void testMultiary() {
		final Valuation val = ImmutableValuation.builder().put(ca, Int(5)).put(cb, Int(9)).build();
		Assert.assertEquals(val.toExpr(), And(Eq(ca.getRef(), Int(5)), Eq(cb.getRef(), Int(9))));
	}

	@Test
	public void testCopy() {
		final Valuation val1 = ImmutableValuation.builder().put(ca, Int(1)).build();
		final MutableValuation val2 = MutableValuation.copyOf(val1);
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(1, val2.getDecls().size());
		val2.put(cb, Int(2));
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(2, val2.getDecls().size());
		final Valuation val3 = ImmutableValuation.copyOf(val2);
		val2.put(cc, Int(3));
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(3, val2.getDecls().size());
		Assert.assertEquals(2, val3.getDecls().size());
	}

	@Test
	public void testLeq() {
		final Valuation v1 = ImmutableValuation.builder().put(ca, Int(1)).build();
		final Valuation v2 = ImmutableValuation.builder().put(ca, Int(2)).build();
		final Valuation v3 = ImmutableValuation.builder().put(cb, Int(1)).build();
		final Valuation v4 = ImmutableValuation.builder().put(ca, Int(1)).put(cb, Int(1)).build();

		Assert.assertTrue(v1.isLeq(v1));
		Assert.assertFalse(v2.isLeq(v1));
		Assert.assertFalse(v3.isLeq(v1));
		Assert.assertTrue(v4.isLeq(v1));

		Assert.assertFalse(v1.isLeq(v2));
		Assert.assertTrue(v2.isLeq(v2));
		Assert.assertFalse(v3.isLeq(v2));
		Assert.assertFalse(v4.isLeq(v2));

		Assert.assertFalse(v1.isLeq(v3));
		Assert.assertFalse(v2.isLeq(v3));
		Assert.assertTrue(v3.isLeq(v3));
		Assert.assertTrue(v4.isLeq(v3));

		Assert.assertFalse(v1.isLeq(v4));
		Assert.assertFalse(v2.isLeq(v4));
		Assert.assertFalse(v3.isLeq(v4));
		Assert.assertTrue(v4.isLeq(v4));
	}

	@Test
	public void testEquals() {
		final Valuation v1 = ImmutableValuation.builder().put(ca, Int(1)).build();
		final Valuation v2 = ImmutableValuation.builder().put(ca, Int(1)).build();
		final Valuation v3 = ImmutableValuation.builder().put(ca, Int(2)).build();
		final Valuation v4 = ImmutableValuation.builder().put(cb, Int(1)).build();

		Assert.assertTrue(v1.equals(v1));
		Assert.assertTrue(v1.equals(v2));
		Assert.assertFalse(v1.equals(v3));
		Assert.assertFalse(v1.equals(v4));

	}
}
