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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class PathUtilsTest {

	final VarDecl<IntType> vx = Decls.Var("x", Int());
	final VarDecl<IntType> vy = Decls.Var("y", Int());
	final VarDecl<IntType> vz = Decls.Var("z", Int());
	final IndexedConstDecl<IntType> x1 = vx.getConstDecl(1);
	final IndexedConstDecl<IntType> x2 = vx.getConstDecl(2);
	final IndexedConstDecl<IntType> y0 = vy.getConstDecl(0);
	final IndexedConstDecl<IntType> y1 = vy.getConstDecl(1);

	@Test
	public void testUnfold() {
		Assert.assertEquals(Eq(x1.getRef(), Add(y0.getRef(), Int(1))),
				PathUtils.unfold(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(x2.getRef(), Add(y1.getRef(), Int(1))),
				PathUtils.unfold(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))), 1));
	}

	@Test
	public void testFold() {
		Assert.assertEquals(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))),
				PathUtils.foldin(Eq(x1.getRef(), Add(y0.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(Prime(vx.getRef(), 2), Add(Prime(vy.getRef()), Int(1))),
				PathUtils.foldin(Eq(x2.getRef(), Add(y1.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))),
				PathUtils.foldin(Eq(x2.getRef(), Add(y1.getRef(), Int(1))), 1));
	}

	@Test
	public void testExtractValuation() {
		final Valuation valuation = ImmutableValuation.builder().put(x1, Int(1)).put(x2, Int(2)).put(y1, Int(3))
				.build();

		final Valuation extr0 = PathUtils.extractValuation(valuation, 1);
		Assert.assertEquals(2, extr0.getDecls().size());
		Assert.assertEquals(Int(1), extr0.eval(vx).get());
		Assert.assertEquals(Int(3), extr0.eval(vy).get());

		final Valuation extr1 = PathUtils.extractValuation(valuation, 1, ImmutableSet.of(vx, vz));
		Assert.assertEquals(1, extr1.getDecls().size());
		Assert.assertEquals(Int(1), extr1.eval(vx).get());
	}
}
