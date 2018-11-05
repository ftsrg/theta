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

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class ExprAtomCollectorTest {

	private static final Expr<BoolType> CA = Const("a", Bool()).getRef();
	private static final Expr<BoolType> CB = Const("b", Bool()).getRef();
	private static final Expr<IntType> CX = Const("x", Int()).getRef();
	private static final Expr<IntType> CY = Const("y", Int()).getRef();

	@Parameter(value = 0)
	public Expr<BoolType> expr;

	@Parameter(value = 1)
	public Set<Expr<BoolType>> expectedAtoms;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ And(CA, Or(CA, Not(CB))), of(CA, CB) },

				{ Imply(Eq(CX, Int(2)), Not(Leq(CX, CY))), of(Eq(CX, Int(2)), Leq(CX, CY)) },

				{ Iff(And(Leq(CX, CY), Eq(CX, CY)), Or(Not(Leq(CX, CY)), CA)), of(CA, Leq(CX, CY), Eq(CX, CY)) },

				{ And(Ite(CA, CA, CB), Not(CA)), of(CA, Ite(CA, CA, CB)) },

		});
	}

	@Test
	public void test() {
		final Set<Expr<BoolType>> atoms = ExprUtils.getAtoms(expr);
		Assert.assertEquals(expectedAtoms, atoms);
	}

}
