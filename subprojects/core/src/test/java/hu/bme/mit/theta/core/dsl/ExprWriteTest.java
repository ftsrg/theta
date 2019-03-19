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
package hu.bme.mit.theta.core.dsl;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
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

import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class ExprWriteTest {

	private static final VarDecl<BoolType> VX = Decls.Var("x", BoolExprs.Bool());
	private static final VarDecl<IntType> VY = Decls.Var("y", Int());

	@Parameter(value = 0)
	public Expr<Type> actual;

	@Parameter(value = 1)
	public String expected;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{And(True(), Or(False(), True(), True())), "true and (false or true or true)"},

				{Iff(Not(True()), Imply(False(), True())), "(not true) iff (false imply true)"},

				{Add(Int(1), Sub(Int(2), Int(3)), Int(4), Neg(Int(5))), "1 + (2 - 3) + 4 + (-5)"},

				{Mul(Int(1), Div(Int(2), Int(3)), Int(4)), "1 * (2 / 3) * 4"},

				{Mul(Mod(Int(4), Int(3)), Rem(Int(4), Int(3))), "(4 mod 3) * (4 rem 3)"},

				{And(Eq(Int(1), Int(1)), Lt(Int(1), Int(2)), Gt(Int(2), Int(1))), "(1 = 1) and (1 < 2) and (2 > 1)"},

				{And(Neq(Int(1), Int(2)), Leq(Int(1), Int(2)), Geq(Int(2), Int(1))),
						"(1 /= 2) and (1 <= 2) and (2 >= 1)"},

				{Add(Rat(1, 2), Sub(Rat(3, 4), Rat(5, 6)), Rat(7, 8), Neg(Rat(9, 1))),
						"1%2 + (3%4 - 5%6) + 7%8 + (-9%1)"},

				{Mul(Rat(1, 2), Div(Rat(3, 4), Rat(5, 6)), Rat(7, 8)), "1%2 * (3%4 / 5%6) * 7%8"},

				{And(Eq(Rat(1, 2), Rat(1, 2)), Lt(Rat(1, 2), Rat(3, 4)), Gt(Rat(3, 4), Rat(1, 2))),
						"(1%2 = 1%2) and (1%2 < 3%4) and (3%4 > 1%2)"},

				{And(Neq(Rat(1, 2), Rat(2, 1)), Leq(Rat(1, 2), Rat(3, 4)), Geq(Rat(3, 4), Rat(1, 2))),
						"(1%2 /= 2%1) and (1%2 <= 3%4) and (3%4 >= 1%2)"},

				{And(VX.getRef(), Eq(VY.getRef(), Int(1))), "x and (y = 1)"},

				{Ite(True(), Int(1), Ite(False(), Int(2), Int(3))), "if true then 1 else (if false then 2 else 3)"},

				{Eq(Prime(Prime(VY.getRef())), Prime(VY.getRef())), "((y')') = (y')"}

		});
	}

	@Test
	public void test() {
		final CoreDslManager manager = new CoreDslManager();
		Assert.assertEquals(expected, manager.writeExpr(actual));
	}
}
