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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Arrays;
import java.util.Collection;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class StmtToExprTransformerTest {

	private static final VarDecl<IntType> VX = Decls.Var("x", Int());
	private static VarDecl<IntType> TEMP0 = VarPoolUtil.requestInt();

	@Parameter(0)
	public Stmt stmt;

	@Parameter(1)
	public Collection<Expr<BoolType>> expectedExprs;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{Stmts.Assume(And(True(), False())), ImmutableList.of(And(True(), False()))},

				{Stmts.Havoc(VX), ImmutableList.of(True())},

				{Stmts.Assign(VX, Int(2)), ImmutableList.of(Eq(Prime(VX.getRef()), Int(2)))},

				{Stmts.SequenceStmt(ImmutableList.of(Stmts.Assume(And(True(), False())))), ImmutableList.of(And(ImmutableList.of(And(True(), False()))))},

				{Stmts.SequenceStmt(ImmutableList.of(Stmts.Assign(VX, Int(2)), Stmts.Assign(VX, Int(2)))), ImmutableList.of(And(Eq(Prime(VX.getRef()), Int(2)), Eq(Prime(Prime(VX.getRef())), Int(2))))},

				{Stmts.NonDetStmt(ImmutableList.of(Stmts.Assume(And(True(), False())))), ImmutableList.of(Or(ImmutableList.of(And(ImmutableList.of(And(Eq(TEMP0.getRef(), Int(0)), And(ImmutableList.of(And(True(), False())))))))))},

				{Stmts.NonDetStmt(ImmutableList.of(Stmts.Assign(VX, Int(2)))), ImmutableList.of(Or(ImmutableList.of(And(ImmutableList.of(And(Eq(TEMP0.getRef(), Int(0)), And(ImmutableList.of(Eq(Prime(VX.getRef()), Int(2))))))))))},

				{Stmts.NonDetStmt(ImmutableList.of(Stmts.Assume(True()), Stmts.Assign(VX, Int(2)))), ImmutableList.of(Or(ImmutableList.of(And(ImmutableList.of(And(Eq(TEMP0.getRef(), Int(0)), And(ImmutableList.of(True()))), Eq(VX.getRef(), Prime(VX.getRef())))), And(ImmutableList.of(And(Eq(TEMP0.getRef(), Int(1)), And(ImmutableList.of(Eq(Prime(VX.getRef()), Int(2))))))))))}

		});
	}

	@Test
	public void test() {
		VarPoolUtil.returnInt(TEMP0);

		final StmtUnfoldResult unfoldResult = StmtUtils.toExpr(stmt, VarIndexing.all(0));
		final Collection<Expr<BoolType>> actualExprs = unfoldResult.getExprs();
		Assert.assertEquals(expectedExprs, actualExprs);
	}
}
