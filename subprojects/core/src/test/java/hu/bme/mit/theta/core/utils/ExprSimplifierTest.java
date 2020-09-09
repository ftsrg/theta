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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
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
import static hu.bme.mit.theta.core.utils.ExprUtils.simplify;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ExprSimplifierTest {

	private final ConstDecl<BoolType> cx = Const("x", Bool());
	private final ConstDecl<BoolType> cy = Const("y", Bool());
	private final ConstDecl<BoolType> cz = Const("z", Bool());
	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());
	private final ConstDecl<IntType> cc = Const("c", Int());
	private final ConstDecl<RatType> cd = Const("d", Rat());
	private final ConstDecl<BvType> ce = Const("e", BvType(4));
	private final ConstDecl<BvType> cf = Const("f", BvType(4));

	private final Expr<BoolType> x = cx.getRef();
	private final Expr<BoolType> y = cy.getRef();
	private final Expr<BoolType> z = cz.getRef();
	private final Expr<IntType> a = ca.getRef();
	private final Expr<IntType> b = cb.getRef();
	private final Expr<IntType> c = cc.getRef();
	private final Expr<RatType> d = cd.getRef();
	private final Expr<BvType> e = ce.getRef();
	private final Expr<BvType> f = cf.getRef();

	// Boolean

	@Test
	public void testNot() {
		assertEquals(False(), simplify(Not(And(True(), True()))));
		assertEquals(True(), simplify(Not(And(False(), True()))));
		assertEquals(x, simplify(Not(Not(Not(Not(x))))));
		assertEquals(Not(x), simplify(Not(Not(Not(x)))));
	}

	@Test
	public void testImply() {
		assertEquals(True(), simplify(Imply(False(), x)));
		assertEquals(True(), simplify(Imply(x, True())));
		assertEquals(x, simplify(Imply(True(), x)));
		assertEquals(Not(x), simplify(Imply(x, False())));
		assertEquals(False(), simplify(Imply(True(), False())));
		assertEquals(True(), simplify(Imply(x, x)));
	}

	@Test
	public void testIff() {
		assertEquals(Not(x), simplify(Iff(False(), x)));
		assertEquals(x, simplify(Iff(x, True())));
		assertEquals(x, simplify(Iff(True(), x)));
		assertEquals(Not(x), simplify(Iff(x, False())));
		assertEquals(True(), simplify(Iff(x, x)));
	}

	@Test
	public void testXor() {
		assertEquals(x, simplify(Xor(False(), x)));
		assertEquals(Not(x), simplify(Xor(x, True())));
		assertEquals(Not(x), simplify(Xor(True(), x)));
		assertEquals(x, simplify(Xor(x, False())));
		assertEquals(False(), simplify(Xor(x, x)));
	}

	@Test
	public void testAnd() {
		assertEquals(x, simplify(And(True(), x, True())));
		assertEquals(False(), simplify(And(True(), x, False())));
		assertEquals(And(x, y, z), simplify(And(x, And(y, z))));
		assertEquals(And(x, z), simplify(And(x, And(True(), z))));
		assertEquals(False(), simplify(And(x, And(False(), z))));
		assertEquals(True(), simplify(And(True(), True())));
	}

	@Test
	public void testOr() {
		assertEquals(x, simplify(Or(False(), x, False())));
		assertEquals(True(), simplify(Or(False(), x, True())));
		assertEquals(Or(x, y, z), simplify(Or(x, Or(y, z))));
		assertEquals(True(), simplify(Or(x, Or(True(), z))));
		assertEquals(Or(x, z), simplify(Or(x, Or(False(), z))));
	}

	// Rational

	@Test
	public void testRatAdd() {
		assertEquals(Rat(7, 12), simplify(Add(Rat(1, 3), Rat(1, 4))));
		assertEquals(Add(Rat(7, 12), d), simplify(Add(Rat(1, 3), d, Rat(1, 4))));
		assertEquals(Add(Rat(7, 12), d), simplify(Add(Rat(1, 3), Add(d, Rat(1, 4)))));
	}

	@Test
	public void testRatSub() {
		assertEquals(Rat(1, 4), simplify(Sub(Rat(3, 4), Rat(1, 2))));
		assertEquals(Rat(-1, 4), simplify(Sub(Rat(3, 4), Rat(1, 1))));
	}

	@Test
	public void testRatNeg() {
		assertEquals(Rat(1, 2), simplify(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
		assertEquals(Rat(-1, 2), simplify(Neg(Neg(Neg(Neg(Neg(Rat(1, 2))))))));
	}

	@Test
	public void testRatMul() {
		assertEquals(Rat(1, 1), simplify(Mul(Rat(2, 1), Rat(1, 1), Rat(1, 2))));
		assertEquals(Rat(3, 4), simplify(Mul(Rat(3, 2), Rat(1, 1), Rat(1, 2))));
		assertEquals(Mul(Rat(3, 4), d), simplify(Mul(Rat(3, 2), d, Rat(1, 2))));
		assertEquals(Mul(Rat(3, 4), d), simplify(Mul(Rat(3, 2), Mul(d, Rat(1, 2)))));
		assertEquals(Rat(0, 1), simplify(Mul(Rat(3, 2), Rat(0, 1), Rat(1, 2))));
	}

	@Test
	public void testRatDiv() {
		assertEquals(Rat(8, 9), simplify(Div(Rat(2, 3), Rat(3, 4))));
		assertEquals(Rat(1, 2), simplify(Div(Rat(2, 3), Rat(4, 3))));
		assertEquals(Rat(1, 3), simplify(Div(Rat(2, 3), Rat(2, 1))));
		assertEquals(Rat(1, 2), simplify(Div(Rat(2, 1), Rat(4, 1))));
		assertEquals(Div(Int(0), a), simplify(Div(Int(0), a)));
	}

	@Test
	public void testRatEq() {
		assertEquals(True(), simplify(Eq(Rat(1, 2), Rat(1, 2))));
		assertEquals(False(), simplify(Eq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testRatNeq() {
		assertEquals(False(), simplify(Neq(Rat(1, 2), Rat(1, 2))));
		assertEquals(True(), simplify(Neq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testRatGeq() {
		assertEquals(True(), simplify(Geq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), simplify(Geq(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), simplify(Geq(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), simplify(Geq(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testRatGt() {
		assertEquals(False(), simplify(Gt(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), simplify(Gt(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), simplify(Gt(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), simplify(Gt(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testRatLeq() {
		assertEquals(True(), simplify(Leq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), simplify(Leq(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), simplify(Leq(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), simplify(Leq(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testRatLt() {
		assertEquals(False(), simplify(Lt(Rat(2, 1), Rat(8, 4))));
		assertEquals(True(), simplify(Lt(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), simplify(Lt(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), simplify(Lt(Rat(9, 4), Rat(2, 1))));
	}

	// Integer

	@Test
	public void testIntToRat() {
		for (int i = -50; i < 50; i++) {
			assertEquals(Rat(i, 1), simplify(ToRat(Int(i))));
		}
	}

	@Test
	public void testIntAdd() {
		assertEquals(Int(6), simplify(Add(Int(1), Int(2), Int(3))));
		assertEquals(Int(0), simplify(Add(Int(1), Int(2), Int(-3))));
		assertEquals(Add(a, Int(4)), simplify(Add(Int(1), a, Int(3))));
		assertEquals(Add(a, Int(4)), simplify(Add(Int(1), Add(a, Int(3)))));
		assertEquals(a, simplify(Add(Int(-3), a, Int(3))));
		assertEquals(Add(a, b, a, b, c), simplify(Add(a, Add(b, Add(a, Add(b, c))))));
		assertEquals(Int("4294967294"), simplify(Add(Int(Integer.MAX_VALUE), Int(Integer.MAX_VALUE))));
	}

	@Test
	public void testIntSub() {
		assertEquals(Int(-1), simplify(Sub(Int(7), Int(8))));
		assertEquals(Int(0), simplify(Sub(a, a)));
	}

	@Test
	public void testIntNeg() {
		assertEquals(Int(182), simplify(Neg(Neg(Neg(Neg(Int(182)))))));
		assertEquals(Int(-182), simplify(Neg(Neg(Neg(Neg(Neg(Int(182))))))));
		assertEquals(a, simplify(Neg(Neg(Neg(Neg(a))))));
		assertEquals(Neg(a), simplify(Neg(Neg(Neg(Neg(Neg(a)))))));
	}

	@Test
	public void testIntMul() {
		assertEquals(Int(30), simplify(Mul(Int(2), Int(3), Int(5))));
		assertEquals(Mul(Int(10), a), simplify(Mul(Int(2), a, Int(5))));
		assertEquals(Mul(Int(10), a), simplify(Mul(Int(2), Mul(a, Int(5)))));
		assertEquals(Int(0), simplify(Mul(Int(0), a, b)));
		assertEquals(Mul(a, b, a, b, c), simplify(Mul(a, Mul(b, Mul(a, Mul(b, c))))));
	}

	@Test
	public void testIntDiv() {
		assertEquals(Int(0), simplify(Div(Int(1), Int(2))));
		assertEquals(Int(1), simplify(Div(Int(3), Int(2))));
		assertEquals(Div(Int(0), a), simplify(Div(Int(0), a)));
	}

	@Test
	public void testMod() {
		assertEquals(Int(1), simplify(Mod(Int(6), Int(5))));
		assertEquals(Int(1), simplify(Mod(Int(6), Int(5))));

		assertEquals(Int(2), simplify(Mod(Int(5), Int(3))));
		assertEquals(Int(1), simplify(Mod(Int(-5), Int(3))));
		assertEquals(Int(2), simplify(Mod(Int(5), Int(-3))));
		assertEquals(Int(1), simplify(Mod(Int(-5), Int(-3))));

		assertEquals(Int(0), simplify(Mod(Int(3), Int(-3))));
		assertEquals(Int(0), simplify(Mod(Int(-3), Int(-3))));
		assertEquals(Int(0), simplify(Mod(Int(-3), Int(3))));
		assertEquals(Int(0), simplify(Mod(Int(3), Int(3))));
	}

	@Test
	public void testIntEq() {
		assertEquals(True(), simplify(Eq(Int(2), Int(2))));
		assertEquals(False(), simplify(Eq(Int(2), Int(-2))));
		assertEquals(True(), simplify(Eq(a, a)));
		assertEquals(Eq(a, b), simplify(Eq(a, b)));
	}

	@Test
	public void testIntNeq() {
		assertEquals(False(), simplify(Neq(Int(2), Int(2))));
		assertEquals(True(), simplify(Neq(Int(2), Int(-2))));
		assertEquals(False(), simplify(Neq(a, a)));
		assertEquals(Neq(a, b), simplify(Neq(a, b)));
	}

	@Test
	public void testIntGeq() {
		assertEquals(True(), simplify(Geq(Int(3), Int(3))));
		assertEquals(True(), simplify(Geq(Int(3), Int(2))));
		assertEquals(False(), simplify(Geq(Int(3), Int(5))));
		assertEquals(True(), simplify(Geq(a, a)));
	}

	@Test
	public void testIntGt() {
		assertEquals(False(), simplify(Gt(Int(3), Int(3))));
		assertEquals(True(), simplify(Gt(Int(3), Int(2))));
		assertEquals(False(), simplify(Gt(Int(3), Int(5))));
		assertEquals(False(), simplify(Gt(a, a)));
	}

	@Test
	public void testIntLeq() {
		assertEquals(True(), simplify(Leq(Int(3), Int(3))));
		assertEquals(False(), simplify(Leq(Int(3), Int(2))));
		assertEquals(True(), simplify(Leq(Int(3), Int(5))));
		assertEquals(True(), simplify(Leq(a, a)));
	}

	@Test
	public void testIntLt() {
		assertEquals(False(), simplify(Lt(Int(3), Int(3))));
		assertEquals(False(), simplify(Lt(Int(3), Int(2))));
		assertEquals(True(), simplify(Lt(Int(3), Int(5))));
		assertEquals(False(), simplify(Lt(a, a)));
	}

	// Bitvectors

	@Test
	public void testBvAdd() {
		assertEquals(
			Bv(new boolean[] {false, false, true, true}),
			simplify(BvExprs.Add(List.of(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, false, false, true})
			)))
		);
		assertEquals(
			BvExprs.Add(List.of(
				e,
				Bv(new boolean[] {false, false, true, true})
			)),
			simplify(BvExprs.Add(List.of(
				Bv(new boolean[] {false, false, true, false}),
				e,
				Bv(new boolean[] {false, false, false, true})
			)))
		);
	}

	@Test
	public void testBvSub() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.Sub(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, false, false, true})
			))
		);
		assertEquals(
			BvExprs.Sub(
				e,
				Bv(new boolean[] {false, false, true, true})
			),
			simplify(BvExprs.Sub(
				e,
				BvExprs.Add(List.of(
					Bv(new boolean[] {false, false, true, false}),
					Bv(new boolean[] {false, false, false, true})
				))
			))
		);
	}

	@Test
	public void testBvNeg() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.Neg(Bv(new boolean[] {true, true, true, true})))
		);
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.Neg(BvExprs.Neg(Bv(new boolean[] {false, false, false, true}))))
		);
	}

	@Test
	public void testBvMul() {
		assertEquals(
			Bv(new boolean[] {false, true, true, false}),
			simplify(BvExprs.Mul(List.of(
				Bv(new boolean[] {false, false, true, true}),
				Bv(new boolean[] {false, false, true, false})
			)))
		);
		assertEquals(
			BvExprs.Mul(List.of(
				Bv(new boolean[] {false, true, true, false}),
				e
			)),
			simplify(BvExprs.Mul(List.of(
				e,
				Bv(new boolean[] {false, false, true, true}),
				Bv(new boolean[] {false, false, true, false})
			)))
		);
	}

	@Test
	public void testBvDiv() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.UDiv(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, true})
			))
		);
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.UDiv(e, e))
		);
	}

	@Test
	public void testBvMod() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.SMod(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, true})
			))
		);
		assertEquals(
			Bv(new boolean[] {false, false, false, false}),
			simplify(BvExprs.SMod(e, e))
		);
	}

	@Test
	public void testBvRem() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.URem(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, true})
			))
		);
		assertEquals(
			Bv(new boolean[] {false, false, false, false}),
			simplify(BvExprs.URem(e, e))
		);
	}

	@Test
	public void testBvAnd() {
		assertEquals(
			Bv(new boolean[] {false, true, false, false}),
			simplify(BvExprs.And(List.of(
				Bv(new boolean[] {false, true, false, true}),
				Bv(new boolean[] {false, true, true, false})
			)))
		);
		assertEquals(
			BvExprs.And(List.of(
				e,
				Bv(new boolean[] {false, true, false, false})
			)),
			simplify(BvExprs.And(List.of(
				e,
				Bv(new boolean[] {false, true, false, true}),
				Bv(new boolean[] {false, true, true, false})
			)))
		);
	}

	@Test
	public void testBvOr() {
		assertEquals(
				Bv(new boolean[] {false, true, true, true}),
				simplify(BvExprs.Or(List.of(
					Bv(new boolean[] {false, true, false, true}),
					Bv(new boolean[] {false, true, true, false})
				)))
		);
		assertEquals(
			BvExprs.Or(List.of(
				e,
				Bv(new boolean[] {false, true, true, true})
			)),
			simplify(BvExprs.Or(List.of(
				e,
				Bv(new boolean[] {false, true, false, true}),
				Bv(new boolean[] {false, true, true, false})
			)))
		);
	}

	@Test
	public void testBvXor() {
		assertEquals(
			Bv(new boolean[] {false, false, true, true}),
			simplify(BvExprs.Xor(List.of(
				Bv(new boolean[] {false, true, false, true}),
				Bv(new boolean[] {false, true, true, false})
			)))
		);
		assertEquals(
			BvExprs.Xor(List.of(
				e,
				Bv(new boolean[] {false, false, true, true})
			)),
			simplify(BvExprs.Xor(List.of(
				e,
				Bv(new boolean[] {false, true, false, true}),
				Bv(new boolean[] {false, true, true, false})
			)))
		);
	}

	@Test
	public void testBvNot() {
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.Not(Bv(new boolean[] {true, true, true, false})))
		);
		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.Not(BvExprs.Not(Bv(new boolean[] {false, false, false, true}))))
		);
	}

	@Test
	public void testBvShift() {
		assertEquals(
			Bv(new boolean[] {false, true, false, false}),
			simplify(BvExprs.ShiftLeft(
				Bv(new boolean[] {false, false, false, true}),
				Bv(new boolean[] {false, false, true, false})
			))
		);

		assertEquals(
			Bv(new boolean[] {false, false, false, true}),
			simplify(BvExprs.ArithShiftRight(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, false})
			))
		);

		assertEquals(
			Bv(new boolean[] {true, true, true, false}),
			simplify(BvExprs.ArithShiftRight(
				Bv(new boolean[] {true, true, false, false}),
				Bv(new boolean[] {false, false, false, true})
			))
		);
	}

	@Test
	public void testBvEq() {
		assertEquals(
			True(),
			simplify(BvExprs.Eq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, true, false, false})
			))
		);
		assertEquals(
			False(),
			simplify(BvExprs.Eq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	@Test
	public void testBvNeq() {
		assertEquals(
			False(),
			simplify(BvExprs.Neq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, true, false, false})
			))
		);
		assertEquals(
			True(),
			simplify(BvExprs.Neq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	@Test
	public void testBvGeq() {
		assertEquals(
			True(),
			simplify(BvExprs.UGeq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, false})
			))
		);
		assertEquals(
			False(),
			simplify(BvExprs.UGeq(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	@Test
	public void testBvGt() {
		assertEquals(
			True(),
			simplify(BvExprs.UGt(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, false})
			))
		);
		assertEquals(
			False(),
			simplify(BvExprs.UGt(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	@Test
	public void testBvLeq() {
		assertEquals(
			False(),
			simplify(BvExprs.ULeq(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, false})
			))
		);
		assertEquals(
			True(),
			simplify(BvExprs.ULeq(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	@Test
	public void testBvLt() {
		assertEquals(
			False(),
			simplify(BvExprs.ULt(
				Bv(new boolean[] {false, true, false, false}),
				Bv(new boolean[] {false, false, true, false})
			))
		);
		assertEquals(
			True(),
			simplify(BvExprs.ULt(
				Bv(new boolean[] {false, false, true, false}),
				Bv(new boolean[] {false, true, false, true})
			))
		);
	}

	// Others

	@Test
	public void testRef() {
		final Valuation val = ImmutableValuation.builder().put(ca, Int(2)).build();
		assertEquals(a, simplify(a));
		assertEquals(Int(2), simplify(a, val));
	}

	@Test
	public void testIte() {
		assertEquals(a, simplify(Ite(True(), a, b)));
		assertEquals(b, simplify(Ite(False(), a, b)));
		assertEquals(a, simplify(Ite(True(), Ite(True(), Ite(True(), a, b), b), b)));
	}

	// Array
	@Test
	public void testArrayRead() {
		var elems = new ArrayList<Tuple2<Expr<IntType>,Expr<IntType>>>();
		elems.add(Tuple2.of(Int(0), Int(1)));
		elems.add(Tuple2.of(Int(1), Int(2)));
		var arr = Array(elems, Int(100), Array(Int(), Int()));
		assertEquals(Int(1), simplify(Read(arr, Int(0))));
		assertEquals(Int(2), simplify(Read(arr, Int(1))));
		assertEquals(Int(100), simplify(Read(arr, Int(182))));
	}

	@Test
	public void testArrayWrite() {
		var elems = new ArrayList<Tuple2<Expr<IntType>,Expr<IntType>>>();
		elems.add(Tuple2.of(Int(0), Int(1)));
		var arr = Array(elems, Int(100), Array(Int(), Int()));
		var newArr = simplify(Write(arr, Int(5), Int(6)));
		assertTrue(newArr instanceof ArrayLitExpr);
		assertEquals(Int(6), Read(newArr, Int(5)).eval(ImmutableValuation.empty()));
		assertEquals(Int(1), Read(newArr, Int(0)).eval(ImmutableValuation.empty()));
		assertEquals(Int(100), Read(newArr, Int(182)).eval(ImmutableValuation.empty()));
	}

	@Test
	public void testComplex() {
		assertEquals(True(), simplify(Iff(And(x, True()), Or(x, False()))));
	}

	@Test
	public void testValuation() {
		final Valuation val = ImmutableValuation.builder().put(ca, Int(5)).put(cb, Int(9)).build();

		assertEquals(Int(14), simplify(Add(a, b), val));
		assertEquals(Add(c, Int(14)), simplify(Add(a, b, c), val));
	}
}
