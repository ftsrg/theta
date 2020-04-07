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

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class StmtToExprTransformerTest {

	private static final VarDecl<IntType> VX = Decls.Var("x", Int());

	@Parameter(0)
	public Stmt stmt;

	@Parameter(1)
	public Collection<Expr<BoolType>> expectedExprs;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{Stmts.Assume(And(True(), False())), ImmutableList.of(And(True(), False()))},

				{Stmts.Havoc(VX), ImmutableList.of(True())},

				{Stmts.Assign(VX, Int(2)), ImmutableList.of(Eq(Prime(VX.getRef()), Int(2)))}

		});
	}

	@Test
	public void test() {

		VarDecl<IntType> VY=Decls.Var("y",Int());

		List<Stmt> stmts=new ArrayList<Stmt>();
		List<Stmt> list1=new ArrayList<Stmt>();
		list1.add(Stmts.Assume(Geq(VX.getRef(),Int(5))));
		list1.add(Stmts.Assign(VX,Int(4)));
		list1.add(Stmts.Assign(VX,Int(2)));
		stmts.add(SequenceStmt.of(list1));
		stmts.add(Stmts.Assume(True()));
		stmts.add(Stmts.Assign(VX,Int(2)));
		stmts.add(Stmts.Assign(VY, Int(3)));
		NonDetStmt nonDetStmt=NonDetStmt.of(stmts);
		StmtUnfoldResult res=StmtUtils.toExpr(nonDetStmt,VarIndexing.all(0));
		System.out.println(nonDetStmt);
		System.out.println(res.exprs);
		System.out.println(res.indexing);

		final StmtUnfoldResult unfoldResult = StmtUtils.toExpr(stmt, VarIndexing.all(0));
		final Collection<Expr<BoolType>> actualExprs = unfoldResult.getExprs();
		Assert.assertEquals(expectedExprs, actualExprs);
	}
}
