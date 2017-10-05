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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
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
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

@RunWith(Parameterized.class)
public class VarCollectorStmtVisitorTest {
	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<BoolType> VB = Var("b", Bool());

	private static final Expr<BoolType> A = VA.getRef();
	private static final Expr<BoolType> B = VB.getRef();

	@Parameter(value = 0)
	public Stmt statement;

	@Parameter(value = 1)
	public Set<VarDecl<?>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Stmts.Assign(VA, B), of(VA, VB) },

				{ Stmts.Assign(VA, True()), of(VA) },

				{ Stmts.Assume(Imply(A, B)), of(VA, VB) },

				{ Stmts.Havoc(VA), of(VA) },

		});
	}

	@Test
	public void test() {
		final Set<VarDecl<?>> vars = StmtUtils.getVars(statement);
		assertEquals(expectedVars, vars);
	}
}
