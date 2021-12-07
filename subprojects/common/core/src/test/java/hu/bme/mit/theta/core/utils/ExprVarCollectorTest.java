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
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Eq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;

@RunWith(Parameterized.class)
public class ExprVarCollectorTest {

	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<IntType> VB = Var("b", Int());
	private static final VarDecl<RatType> VC = Var("c", Rat());
	private static final VarDecl<BoolType> VD = Var("d", Bool());

	private static final Expr<BoolType> A = VA.getRef();
	private static final Expr<IntType> B = VB.getRef();
	private static final Expr<RatType> C = VC.getRef();
	private static final Expr<BoolType> D = VD.getRef();

	@Parameter(value = 0)
	public Expr<Type> expr;

	@Parameter(value = 1)
	public Set<VarDecl<?>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{And(True(), False(), Eq(Int(1), Int(2))), of()},

				{And(A, Not(D)), of(VA, VD)},

				{And(A, Eq(Int(1), B)), of(VA, VB)},

				{And(Imply(A, D), Eq(C, Rat(2, 3))), of(VA, VC, VD)},});
	}

	@Test
	public void test() {
		final Set<VarDecl<?>> vars = ExprUtils.getVars(expr);
		assertEquals(expectedVars, vars);
	}

}
