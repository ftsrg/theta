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
		final Valuation val = BasicValuation.empty();
		Assert.assertEquals(val.toExpr(), True());
	}

	@Test
	public void testUnary() {
		final Valuation val = BasicValuation.builder().put(ca, Int(5)).build();
		Assert.assertEquals(val.toExpr(), Eq(ca.getRef(), Int(5)));
	}

	@Test
	public void testMultiary() {
		final Valuation val = BasicValuation.builder().put(ca, Int(5)).put(cb, Int(9)).build();
		Assert.assertEquals(val.toExpr(), And(Eq(ca.getRef(), Int(5)), Eq(cb.getRef(), Int(9))));
	}

	@Test
	public void testCopy() {
		final Valuation val1 = BasicValuation.builder().put(ca, Int(1)).build();
		final MutableValuation val2 = MutableValuation.copyOf(val1);
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(1, val2.getDecls().size());
		val2.put(cb, Int(2));
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(2, val2.getDecls().size());
		final Valuation val3 = BasicValuation.copyOf(val2);
		val2.put(cc, Int(3));
		Assert.assertEquals(1, val1.getDecls().size());
		Assert.assertEquals(3, val2.getDecls().size());
		Assert.assertEquals(2, val3.getDecls().size());
	}
}
