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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class PredOrdTest {
	private final VarDecl<IntType> VX = Decls.Var("x", Int());

	private final PredOrd ord = PredOrd.create(Z3SolverFactory.getInstance().createSolver());

	PredState sb = PredState.of(False());
	PredState s1 = PredState.of(Gt(VX.getRef(), Int(1)));
	PredState s2 = PredState.of(Gt(VX.getRef(), Int(0)));
	PredState s3 = PredState.of(Lt(VX.getRef(), Int(5)));
	PredState st = PredState.of();

	@Test
	public void testBottom() {
		Assert.assertTrue(sb.isBottom());
		Assert.assertFalse(s1.isBottom());
		Assert.assertFalse(s2.isBottom());
		Assert.assertFalse(s3.isBottom());
		Assert.assertFalse(st.isBottom());
	}

	@Test
	public void testLeq() {
		Assert.assertTrue(ord.isLeq(sb, sb));
		Assert.assertTrue(ord.isLeq(sb, s1));
		Assert.assertTrue(ord.isLeq(sb, s2));
		Assert.assertTrue(ord.isLeq(sb, s3));
		Assert.assertTrue(ord.isLeq(sb, st));

		Assert.assertFalse(ord.isLeq(s1, sb));
		Assert.assertTrue(ord.isLeq(s1, s1));
		Assert.assertTrue(ord.isLeq(s1, s2));
		Assert.assertFalse(ord.isLeq(s1, s3));
		Assert.assertTrue(ord.isLeq(s1, st));

		Assert.assertFalse(ord.isLeq(s2, sb));
		Assert.assertFalse(ord.isLeq(s2, s1));
		Assert.assertTrue(ord.isLeq(s2, s2));
		Assert.assertFalse(ord.isLeq(s2, s3));
		Assert.assertTrue(ord.isLeq(s2, st));

		Assert.assertFalse(ord.isLeq(st, sb));
		Assert.assertFalse(ord.isLeq(st, s1));
		Assert.assertFalse(ord.isLeq(st, s2));
		Assert.assertFalse(ord.isLeq(st, s3));
		Assert.assertTrue(ord.isLeq(st, st));
	}
}
