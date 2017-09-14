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

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Block;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolType;

@RunWith(Parameterized.class)
public class SubStmtTest {

	private static final VarDecl<BoolType> VA = Var("a", Bool());

	@Parameter(value = 0)
	public Stmt statement;

	@Parameter(value = 1)
	public List<? extends Stmt> expectedSubStmts;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Skip(), of(Skip()) },

				{ Havoc(VA), of(Havoc(VA)) },

				{ Block(of(Skip(), Havoc(VA))), of(Skip(), Havoc(VA)) },

				{ Block(of(Skip(), Block(of(Havoc(VA), Assign(VA, True()))))),
						of(Skip(), Havoc(VA), Assign(VA, True())) },

		});
	}

	@Test
	public void test() {
		final List<? extends Stmt> subStmts = StmtUtils.getSubStmts(statement);
		assertEquals(expectedSubStmts, subStmts);
	}
}
