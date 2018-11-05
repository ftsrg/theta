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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import com.google.common.collect.ImmutableMap;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class ExprIndexedVarCollectorTest {
	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<IntType> VB = Var("b", Int());

	private static final IndexedConstDecl<BoolType> A0 = VA.getConstDecl(0);
	private static final IndexedConstDecl<BoolType> A1 = VA.getConstDecl(1);
	private static final IndexedConstDecl<BoolType> A2 = VA.getConstDecl(2);
	private static final IndexedConstDecl<IntType> B0 = VB.getConstDecl(0);
	private static final IndexedConstDecl<IntType> B1 = VB.getConstDecl(1);

	@Parameter(value = 0)
	public Expr<Type> expr;

	@Parameter(value = 1)
	public Map<Integer, Set<VarDecl<?>>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ And(True(), False(), Eq(Int(1), Int(2))), ImmutableMap.of() },

				{ And(A0.getRef(), Not(A1.getRef())), ImmutableMap.of(0, of(VA), 1, of(VA)) },

				{ And(A2.getRef(), A0.getRef(), Eq(B0.getRef(), B1.getRef())),
						ImmutableMap.of(0, of(VA, VB), 1, of(VB), 2, of(VA)) },

		});

	}

	@Test
	public void test() {
		final IndexedVars actualVars = ExprUtils.getVarsIndexed(expr);

		Assert.assertEquals(expectedVars.keySet(), actualVars.getNonEmptyIndexes());

		for (final Entry<Integer, Set<VarDecl<?>>> entry : expectedVars.entrySet()) {
			Assert.assertEquals(entry.getValue(), actualVars.getVars(entry.getKey()));
		}

		Assert.assertEquals(expectedVars.values().stream().flatMap(s -> s.stream()).collect(Collectors.toSet()),
				actualVars.getAllVars());
	}
}
