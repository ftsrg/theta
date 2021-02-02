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

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static hu.bme.mit.theta.core.utils.ExprUtils.eliminateIte;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExprIteEliminatorTest {

	// Constants for testing
	private Expr<BoolType> a, b, c, d, e;
	private Expr<IntType> x, y, z, t;
	private Expr<IntType> i1, i2, i3, i4, i5;

	@Before
	public void before() {

		// Create constants
		a = Const("a", Bool()).getRef();
		b = Const("b", Bool()).getRef();
		c = Const("c", Bool()).getRef();
		d = Const("d", Bool()).getRef();
		e = Const("e", Bool()).getRef();
		x = Const("x", Int()).getRef();
		y = Const("y", Int()).getRef();
		z = Const("z", Int()).getRef();
		t = Const("t", Int()).getRef();
		i1 = Int(1);
		i2 = Int(2);
		i3 = Int(3);
		i4 = Int(4);
		i5 = Int(5);
	}

	@Test
	public void testSimple() {
		// if A then B else C
		assertEquals(eliminateIte(Ite(a, b, c)), And(Or(Not(a), b), Or(a, c)));

		// if A then (if B then C else D) else E
		assertEquals(eliminateIte(Ite(a, Ite(b, c, d), e)), And(Or(Not(a), And(Or(Not(b), c), Or(b, d))), Or(a, e)));
	}

	@Test
	public void testUnary() {
		// !(if A then B else C)
		assertEquals(eliminateIte(Not(Ite(a, b, c))), Not(And(Or(Not(a), b), Or(a, c))));
	}

	@Test
	public void testBinary() {
		// A -> (if B then C else D)
		assertEquals(eliminateIte(Imply(a, Ite(b, c, d))), Imply(a, And(Or(Not(b), c), Or(b, d))));
		// (if B then C else D) -> A
		assertEquals(eliminateIte(Imply(Ite(b, c, d), a)), Imply(And(Or(Not(b), c), Or(b, d)), a));
		// A = (if B then C else D)
		assertEquals(eliminateIte(Iff(a, Ite(b, c, d))), Iff(a, And(Or(Not(b), c), Or(b, d))));
		// X = (if A then Y else Z)
		assertEquals(eliminateIte(Eq(x, Ite(a, y, z))), And(Or(Not(a), Eq(x, y)), Or(a, Eq(x, z))));
		// (if A then Y else Z) = X
		assertEquals(eliminateIte(Eq(Ite(a, y, z), x)), And(Or(Not(a), Eq(y, x)), Or(a, Eq(z, x))));
		// X = (if A then (if B then Y else Z) else T)
		assertEquals(eliminateIte(Eq(x, Ite(a, Ite(b, y, z), t))),
				And(Or(Not(a), And(Or(Not(b), Eq(x, y)), Or(b, Eq(x, z)))), Or(a, Eq(x, t))));
		// (if A then (if B then Y else Z) else T) = X
		assertEquals(eliminateIte(Eq(Ite(a, Ite(b, y, z), t), x)),
				And(Or(Not(a), And(Or(Not(b), Eq(y, x)), Or(b, Eq(z, x)))), Or(a, Eq(t, x))));
		// (if A then X else Y) = (if B then Z else T)
		assertEquals(eliminateIte(Eq(Ite(a, x, y), Ite(b, z, t))),
				And(Or(Not(a), And(Or(Not(b), Eq(x, z)), Or(b, Eq(x, t)))),
						Or(a, And(Or(Not(b), Eq(y, z)), Or(b, Eq(y, t))))));
	}

	@Test
	public void testMultiary() {
		// A or B or (if C then D else E)
		assertEquals(eliminateIte(Or(a, b, Ite(c, d, e))), Or(a, b, And(Or(Not(c), d), Or(c, e))));
		// 1 = 2 + (if A then 3 else 4) + 5
		assertEquals(eliminateIte(Eq(i1, Add(i2, Ite(a, i3, i4), i5))),
				And(Or(Not(a), Eq(i1, Add(i2, i3, i5))), Or(a, Eq(i1, Add(i2, i4, i5)))));
		// 1 = 2 + (if A then 3 else 4) + (if B then X else Y)
		assertEquals(eliminateIte(Eq(i1, Add(i2, Ite(a, i3, i4), Ite(b, x, y)))),
				And(Or(Not(a), And(Or(Not(b), Eq(i1, Add(i2, i3, x))), Or(b, Eq(i1, Add(i2, i3, y))))),
						Or(a, And(Or(Not(b), Eq(i1, Add(i2, i4, x))), Or(b, Eq(i1, Add(i2, i4, y)))))));
	}

	@Test
	public void testNothingHappening() {
		final List<Expr<BoolType>> expressions = new ArrayList<>();
		expressions.add(And(a, b, d));
		expressions.add(Eq(x, Neg(y)));
		expressions.add(Geq(Sub(x, y), Add(x, z, t)));

		for (final Expr<BoolType> expr : expressions) {
			assertEquals(expr, eliminateIte(expr));
		}
	}

	@Test
	public void testPrime() {
		// D = (if A then X else Y)'
		assertEquals(eliminateIte(Eq(z, Prime(Ite(a, x, y)))),
				And(Or(Not(a), Eq(z, Prime(x))), Or(a, Eq(z, Prime(y)))));
	}
}
