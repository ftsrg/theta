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
package hu.bme.mit.theta.core.parser;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static org.junit.Assert.assertEquals;

import java.io.Reader;
import java.io.StringReader;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public final class CoreParserTest {

	private static final Decl<BoolType> DX = Const("x", Bool());
	private static final Decl<BoolType> DY = Const("y", Bool());
	private static final Decl<BoolType> DZ = Const("z", Bool());
	private static final Decl<IntType> DA = Const("a", Int());
	private static final Decl<IntType> DB = Const("b", Int());
	private static final Decl<IntType> DC = Const("c", Int());
	private static final Decl<FuncType<IntType, BoolType>> DF = Const("f", Func(Int(), Bool()));

	private static final Expr<BoolType> X = DX.getRef();
	private static final Expr<BoolType> Y = DY.getRef();
	private static final Expr<BoolType> Z = DZ.getRef();
	private static final Expr<IntType> A = DA.getRef();
	private static final Expr<IntType> B = DB.getRef();
	private static final Expr<IntType> C = DC.getRef();
	private static final Expr<FuncType<IntType, BoolType>> F = DF.getRef();

	@Parameter(0)
	public String string;

	@Parameter(1)
	public Expr<?> expectedExpr;

	private CoreParser parser;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "true", True() },

				{ "false", False() },

				{ "(not x)", Not(X) },

				{ "(and x y z)", And(X, Y, Z) },

				{ "(or x y z)", Or(X, Y, Z) },

				{ "(=> x y)", Imply(X, Y) },

				{ "(iff x y)", Iff(X, Y) },

				{ "(xor x y)", Xor(X, Y) },

				{ "1", Int(1) },

				{ "(+ a b c)", Add(A, B, C) },

				{ "(* a b c)", Mul(A, B, C) },

				{ "(- a b)", Sub(A, B) },

				{ "(/ a b)", Div(A, B) },

				{ "(mod a b)", Mod(A, B) },

				{ "(rem a b)", Rem(A, B) },

				{ "(< a b)", Lt(A, B) },

				{ "(<= a b)", Leq(A, B) },

				{ "(> a b)", Gt(A, B) },

				{ "(>= a b)", Geq(A, B) },

				{ "(= a b)", Eq(A, B) },

				{ "(/= a b)", Neq(A, B) },

				{ "a", A },

				{ "(ite x a b)", Ite(X, A, B) },

				{ "(f a)", App(F, A) }

		});
	}

	@Before
	public void before() {
		final Reader reader = new StringReader(string);
		parser = new CoreParser(reader);
		parser.declare(DX);
		parser.declare(DY);
		parser.declare(DZ);
		parser.declare(DA);
		parser.declare(DB);
		parser.declare(DC);
		parser.declare(DF);
	}

	@Test
	public void test() {
		// Act
		final Expr<?> actualExpr = parser.expr();

		// Assert
		assertEquals(expectedExpr, actualExpr);
	}

}
