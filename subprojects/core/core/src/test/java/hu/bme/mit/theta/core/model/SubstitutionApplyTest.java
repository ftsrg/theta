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
package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class SubstitutionApplyTest {

	private static final VarDecl<IntType> VA = Var("a", Int());
	private static final VarDecl<IntType> VB = Var("b", Int());

	private static final Expr<IntType> A = VA.getRef();
	private static final Expr<IntType> B = VB.getRef();

	@Parameter(value = 0)
	public Expr<Type> expr;

	@Parameter(value = 1)
	public Substitution sub;

	@Parameter(value = 2)
	public Expr<Type> expected;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{Add(B, Int(3)), BasicSubstitution.builder().build(), Add(B, Int(3))},

				{Add(B, Int(3)), BasicSubstitution.builder().put(VB, Add(Int(1), Int(2))).build(),
						Add(Add(Int(1), Int(2)), Int(3))},

				{Add(B, Int(3)), BasicSubstitution.builder().put(VB, Add(B, Int(2))).build(),
						Add(Add(B, Int(2)), Int(3))},

				{Div(B, A), BasicSubstitution.builder().put(VB, A).put(VA, B).build(), Div(A, B)},

		});
	}

	@Test
	public void test() {
		assertEquals(expected, sub.apply(expr));
	}
}
