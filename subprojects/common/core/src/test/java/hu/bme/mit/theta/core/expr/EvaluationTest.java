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
package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.ToRat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Div;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Eq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Geq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Gt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Leq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Lt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Mul;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Neg;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Neq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Sub;
import static org.junit.Assert.assertEquals;

import hu.bme.mit.theta.common.Tuple2;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.ArrayList;

public class EvaluationTest {

	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());
	private final Expr<IntType> a = ca.getRef();
	private final Expr<IntType> b = cb.getRef();

	private static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr) {
		return expr.eval(ImmutableValuation.empty());
	}

	private static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr, final Valuation val) {
		return expr.eval(val);
	}

	// booltype

	@Test
	public void testAnd() {
		assertEquals(False(), evaluate(And(True(), False(), True())));
		assertEquals(True(), evaluate(And(True(), True(), True())));
	}

	@Test
	public void testFalse() {
		assertEquals(False(), evaluate(False()));
	}

	@Test
	public void testIff() {
		assertEquals(False(), evaluate(Iff(False(), True())));
		assertEquals(True(), evaluate(Iff(True(), True())));
		assertEquals(False(), evaluate(Iff(True(), False())));
		assertEquals(True(), evaluate(Iff(False(), False())));
	}

	@Test
	public void testImply() {
		assertEquals(True(), evaluate(Imply(False(), True())));
		assertEquals(True(), evaluate(Imply(True(), True())));
		assertEquals(False(), evaluate(Imply(True(), False())));
		assertEquals(True(), evaluate(Imply(False(), False())));
	}

	@Test
	public void testNot() {
		assertEquals(False(), evaluate(Not(And(True(), True()))));
		assertEquals(True(), evaluate(Not(And(False(), True()))));
	}

	@Test
	public void testOr() {
		assertEquals(False(), evaluate(Or(False(), False(), False())));
		assertEquals(True(), evaluate(Or(False(), True(), False())));
	}

	@Test
	public void testTrue() {
		assertEquals(True(), evaluate(True()));
	}

	@Test
	public void testXor() {
		assertEquals(True(), evaluate(Xor(False(), True())));
		assertEquals(False(), evaluate(Xor(True(), True())));
		assertEquals(True(), evaluate(Xor(True(), False())));
		assertEquals(False(), evaluate(Xor(False(), False())));
	}

	// inttype

	@Test
	public void testIntAdd() {
		assertEquals(Int(6), evaluate(Add(Int(1), Int(2), Int(3))));
		assertEquals(Int(0), evaluate(Add(Int(1), Int(2), Int(-3))));
	}

	@Test
	public void testIntDiv() {
		assertEquals(Int(0), evaluate(Div(Int(1), Int(2))));
		assertEquals(Int(1), evaluate(Div(Int(3), Int(2))));
	}

	@Test
	public void testIntEq() {
		assertEquals(True(), evaluate(Eq(Int(2), Int(2))));
		assertEquals(False(), evaluate(Eq(Int(2), Int(-2))));
	}

	@Test
	public void testIntGeq() {
		assertEquals(True(), evaluate(Geq(Int(2), Int(1))));
		assertEquals(True(), evaluate(Geq(Int(1), Int(1))));
		assertEquals(False(), evaluate(Geq(Int(1), Int(2))));
	}

	@Test
	public void testIntGt() {
		assertEquals(True(), evaluate(Gt(Int(2), Int(1))));
		assertEquals(False(), evaluate(Gt(Int(1), Int(1))));
		assertEquals(False(), evaluate(Gt(Int(1), Int(2))));
	}

	@Test
	public void testIntLeq() {
		assertEquals(False(), evaluate(Leq(Int(2), Int(1))));
		assertEquals(True(), evaluate(Leq(Int(1), Int(1))));
		assertEquals(True(), evaluate(Leq(Int(1), Int(2))));
	}

	@Test
	public void testIntLit() {
		for (int i = -10; i <= 10; ++i) {
			assertEquals(Int(i), evaluate(Int(i)));
		}
	}

	@Test
	public void testIntLt() {
		assertEquals(False(), evaluate(Lt(Int(2), Int(1))));
		assertEquals(False(), evaluate(Lt(Int(1), Int(1))));
		assertEquals(True(), evaluate(Lt(Int(1), Int(2))));
	}

	@Test
	public void testIntMul() {
		assertEquals(Int(30), evaluate(Mul(Int(2), Int(3), Int(5))));
		assertEquals(Int(-30), evaluate(Mul(Int(2), Int(-3), Int(5))));
		assertEquals(Int(30), evaluate(Mul(Int(2), Int(-3), Int(-5))));
		assertEquals(Int(0), evaluate(Mul(Int(2), Int(0), Int(5))));
	}

	@Test
	public void testIntNeg() {
		assertEquals(Int(182), evaluate(Neg(Neg(Neg(Neg(Int(182)))))));
		assertEquals(Int(-182), evaluate(Neg(Neg(Neg(Neg(Neg(Int(182))))))));
	}

	@Test
	public void testIntNeq() {
		assertEquals(False(), evaluate(Neq(Int(2), Int(2))));
		assertEquals(True(), evaluate(Neq(Int(2), Int(-2))));
	}

	@Test
	public void testIntSub() {
		assertEquals(Int(-1), evaluate(Sub(Int(7), Int(8))));
		assertEquals(Int(2), evaluate(Sub(Int(5), Int(3))));
	}

	@Test
	public void testIntToRat() {
		for (int i = -10; i <= 10; ++i) {
			assertEquals(Rat(i, 1), evaluate(ToRat(Int(i))));
		}
	}

	@Test
	public void testMod() {
		assertEquals(Int(2), evaluate(Mod(Int(2), Int(3))));

		assertEquals(Int(2), evaluate(Mod(Int(5), Int(3))));
		assertEquals(Int(1), evaluate(Mod(Int(-5), Int(3))));
		assertEquals(Int(2), evaluate(Mod(Int(5), Int(-3))));
		assertEquals(Int(1), evaluate(Mod(Int(-5), Int(-3))));

		assertEquals(Int(0), evaluate(Mod(Int(3), Int(-3))));
		assertEquals(Int(0), evaluate(Mod(Int(-3), Int(-3))));
		assertEquals(Int(0), evaluate(Mod(Int(-3), Int(3))));
		assertEquals(Int(0), evaluate(Mod(Int(3), Int(3))));
	}

	@Test
	public void testRem() {
		assertEquals(Int(2), evaluate(Rem(Int(2), Int(3))));

		assertEquals(Int(2), evaluate(Rem(Int(5), Int(3))));
		assertEquals(Int(1), evaluate(Rem(Int(-5), Int(3))));
		assertEquals(Int(-2), evaluate(Rem(Int(5), Int(-3))));
		assertEquals(Int(-1), evaluate(Rem(Int(-5), Int(-3))));

		assertEquals(Int(0), evaluate(Rem(Int(3), Int(-3))));
		assertEquals(Int(0), evaluate(Rem(Int(-3), Int(-3))));
		assertEquals(Int(0), evaluate(Rem(Int(-3), Int(3))));
		assertEquals(Int(0), evaluate(Rem(Int(3), Int(3))));
	}

	// rattype

	@Test
	public void testRatAdd() {
		assertEquals(Rat(7, 12), evaluate(Add(Rat(1, 3), Rat(1, 4))));
	}

	@Test
	public void testRatDiv() {
		assertEquals(Rat(8, 9), evaluate(Div(Rat(2, 3), Rat(3, 4))));
		assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 3), Rat(4, 3))));
		assertEquals(Rat(1, 3), evaluate(Div(Rat(2, 3), Rat(2, 1))));
		assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 1), Rat(4, 1))));
	}

	@Test
	public void testRatEq() {
		assertEquals(True(), evaluate(Eq(Rat(1, 2), Rat(1, 2))));
		assertEquals(False(), evaluate(Eq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testRatGeq() {
		assertEquals(True(), evaluate(Geq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Geq(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), evaluate(Geq(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), evaluate(Geq(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testRatGt() {
		assertEquals(False(), evaluate(Gt(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Gt(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), evaluate(Gt(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), evaluate(Gt(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testRatLeq() {
		assertEquals(True(), evaluate(Leq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Leq(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), evaluate(Leq(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), evaluate(Leq(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testRatLit() {
		assertEquals(Rat(1, 2), evaluate(Rat(1, 2)));
	}

	@Test
	public void testRatLt() {
		assertEquals(False(), evaluate(Lt(Rat(2, 1), Rat(8, 4))));
		assertEquals(True(), evaluate(Lt(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), evaluate(Lt(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), evaluate(Lt(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testRatMul() {
		assertEquals(Rat(1, 1), evaluate(Mul(Rat(2, 1), Rat(1, 1), Rat(1, 2))));
		assertEquals(Rat(3, 4), evaluate(Mul(Rat(3, 2), Rat(1, 1), Rat(1, 2))));
	}

	@Test
	public void testRatNeg() {
		assertEquals(Rat(1, 2), evaluate(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
		assertEquals(Rat(-1, 2), evaluate(Neg(Neg(Neg(Neg(Neg(Rat(1, 2))))))));
	}

	@Test
	public void testRatNeq() {
		assertEquals(False(), evaluate(Neq(Rat(1, 2), Rat(1, 2))));
		assertEquals(True(), evaluate(Neq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testRatSub() {
		assertEquals(Rat(1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 2))));
		assertEquals(Rat(-1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 1))));
	}

	// arraytype

	@Test
	public void testRead() {
		var elems = new ArrayList<Tuple2<Expr<IntType>,Expr<IntType>>>();
		elems.add(Tuple2.of(Int(0), Int(1)));
		elems.add(Tuple2.of(Int(1), Int(2)));
		var arr = Array(elems, Int(100), Array(Int(), Int()));
		assertEquals(Int(1), evaluate(Read(arr, Int(0))));
		assertEquals(Int(2), evaluate(Read(arr, Int(1))));
		assertEquals(Int(100), evaluate(Read(arr, Int(5))));
	}

	@Test
	public void testWrite() {
		var elems = new ArrayList<Tuple2<Expr<IntType>,Expr<IntType>>>();
		elems.add(Tuple2.of(Int(0), Int(1)));
		elems.add(Tuple2.of(Int(1), Int(2)));
		var arr = Array(elems, Int(100), Array(Int(), Int()));

		var arr1 = Write(arr, Int(0), Int(34));
		assertEquals(Int(34), evaluate(Read(arr1, Int(0))));
		assertEquals(Int(2), evaluate(Read(arr1, Int(1))));
		assertEquals(Int(100), evaluate(Read(arr1, Int(5))));

		var arr2 = Write(arr, Int(2), Int(34));
		assertEquals(Int(1), evaluate(Read(arr2, Int(0))));
		assertEquals(Int(2), evaluate(Read(arr2, Int(1))));
		assertEquals(Int(34), evaluate(Read(arr2, Int(2))));
		assertEquals(Int(100), evaluate(Read(arr2, Int(5))));
	}

	// anytype

	@Test
	public void testIte() {
		assertEquals(Int(1), evaluate(Ite(True(), Int(1), Int(2))));
		assertEquals(Int(2), evaluate(Ite(False(), Int(1), Int(2))));
		assertEquals(Int(1), evaluate(Ite(True(), Ite(True(), Ite(True(), Int(1), Int(2)), Int(3)), Int(4))));
	}

	@Test
	public void testValuation() {
		final Valuation val = ImmutableValuation.builder().put(ca, Int(5)).put(cb, Int(10)).build();
		assertEquals(Int(15), evaluate(Add(a, b), val));
		assertEquals(Int(50), evaluate(Mul(a, b), val));
		assertEquals(Int(0), evaluate(Div(a, b), val));
	}

	@Test(expected = RuntimeException.class)
	public void testException() {
		evaluate(Add(a, Int(1)));
	}
}
