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
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplDomainTest {

	final VarDecl<IntType> X = Decls.Var("x", Int());
	final VarDecl<IntType> Y = Decls.Var("y", Int());

	final ExplDomain domain = ExplDomain.getInstance();

	final ExplState st = ExplState.createTop();
	final ExplState s1 = ExplState.create(BasicValuation.builder().put(X, Int(1)).build());
	final ExplState s2 = ExplState.create(BasicValuation.builder().put(X, Int(2)).build());
	final ExplState s3 = ExplState.create(BasicValuation.builder().put(Y, Int(1)).build());
	final ExplState s4 = ExplState.create(BasicValuation.builder().put(X, Int(1)).put(Y, Int(1)).build());
	final ExplState sb = ExplState.createBottom();

	@Test
	public void testBottom() {
		Assert.assertFalse(domain.isBottom(st));
		Assert.assertFalse(domain.isBottom(s1));
		Assert.assertFalse(domain.isBottom(s2));
		Assert.assertFalse(domain.isBottom(s3));
		Assert.assertFalse(domain.isBottom(s4));
		Assert.assertTrue(domain.isBottom(sb));
	}

	@Test
	public void testLeq() {
		Assert.assertTrue(domain.isLeq(st, st));
		Assert.assertTrue(domain.isLeq(s1, st));
		Assert.assertTrue(domain.isLeq(s2, st));
		Assert.assertTrue(domain.isLeq(s3, st));
		Assert.assertTrue(domain.isLeq(s4, st));
		Assert.assertTrue(domain.isLeq(sb, st));

		Assert.assertFalse(domain.isLeq(st, s1));
		Assert.assertTrue(domain.isLeq(s1, s1));
		Assert.assertFalse(domain.isLeq(s2, s1));
		Assert.assertFalse(domain.isLeq(s3, s1));
		Assert.assertTrue(domain.isLeq(s4, s1));
		Assert.assertTrue(domain.isLeq(sb, s1));

		Assert.assertFalse(domain.isLeq(st, s2));
		Assert.assertFalse(domain.isLeq(s1, s2));
		Assert.assertTrue(domain.isLeq(s2, s2));
		Assert.assertFalse(domain.isLeq(s3, s2));
		Assert.assertFalse(domain.isLeq(s4, s2));
		Assert.assertTrue(domain.isLeq(sb, s2));

		Assert.assertFalse(domain.isLeq(st, s3));
		Assert.assertFalse(domain.isLeq(s1, s3));
		Assert.assertFalse(domain.isLeq(s2, s3));
		Assert.assertTrue(domain.isLeq(s3, s3));
		Assert.assertTrue(domain.isLeq(s4, s3));
		Assert.assertTrue(domain.isLeq(sb, s3));

		Assert.assertFalse(domain.isLeq(st, s4));
		Assert.assertFalse(domain.isLeq(s1, s4));
		Assert.assertFalse(domain.isLeq(s2, s4));
		Assert.assertFalse(domain.isLeq(s3, s4));
		Assert.assertTrue(domain.isLeq(s4, s4));
		Assert.assertTrue(domain.isLeq(sb, s4));

		Assert.assertFalse(domain.isLeq(st, sb));
		Assert.assertFalse(domain.isLeq(s1, sb));
		Assert.assertFalse(domain.isLeq(s2, sb));
		Assert.assertFalse(domain.isLeq(s3, sb));
		Assert.assertFalse(domain.isLeq(s4, sb));
		Assert.assertTrue(domain.isLeq(sb, sb));
	}
}
