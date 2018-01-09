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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class PredPrecTest {

	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	private final Expr<BoolType> pred = Lt(x.getRef(), Int(5));

	@Test
	public void testRefinement() {
		final PredPrec p0 = PredPrec.of();
		final PredPrec p1 = PredPrec.of(Collections.singleton(pred));
		final PredPrec p2 = PredPrec.of(Collections.singleton(Eq(x.getRef(), y.getRef())));

		final PredPrec r1 = p1.join(p0);
		final PredPrec r2 = p1.join(p2);
		final PredPrec r3 = p1.join(r2);

		Assert.assertSame(p1, r1);
		Assert.assertNotSame(p1, r2);
		Assert.assertSame(r2, r3);

	}

	@Test
	public void testEquals() {
		final PredPrec p0 = PredPrec.of();
		final PredPrec p1 = PredPrec.of(Collections.singleton(pred));
		final PredPrec p2 = PredPrec.of(Collections.singleton(pred));

		Assert.assertNotEquals(p0, p1);
		Assert.assertNotEquals(p0, p2);
		Assert.assertEquals(p1, p2);
	}
}
