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

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.util.Collection;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static java.util.Arrays.asList;
import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public final class PrimeCounterTest {

	@Parameter(value = 0)
	public String exprString;

	@Parameter(value = 1)
	public int nPrimesOnX;

	@Parameter(value = 2)
	public int nPrimesOnY;

	@Parameters
	public static Collection<Object[]> data() {
		return asList(new Object[][]{

				{"true", 0, 0},

				{"(true)'", 0, 0},

				{"x", 0, 0},

				{"not x'", 1, 0},

				{"x''", 2, 0},

				{"x' and y", 1, 0},

				{"(x imply y)'", 1, 1},

				{"(x' iff y)'", 2, 1},

				{"a", 0, 0},

				{"a'", 0, 0},

				{"x' and a", 1, 0},

				{"(x' or a)'", 2, 0}

		});
	}

	@Test
	public void test() {
		// Arrange
		final ConstDecl<BoolType> a = Const("a", Bool());
		final VarDecl<BoolType> x = Var("x", Bool());
		final VarDecl<BoolType> y = Var("y", Bool());

		final CoreDslManager manager = new CoreDslManager();
		manager.declare(a);
		manager.declare(x);
		manager.declare(y);

		final Expr<?> expr = manager.parseExpr(exprString);

		// Act
		final VarIndexing indexing = PathUtils.countPrimes(expr);

		// Assert
		assertEquals(nPrimesOnX, indexing.get(x));
		assertEquals(nPrimesOnY, indexing.get(y));
	}

}
