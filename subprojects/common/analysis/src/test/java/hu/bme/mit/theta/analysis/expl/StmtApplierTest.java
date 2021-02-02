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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult.BOTTOM;
import static hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult.FAILURE;
import static hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult.SUCCESS;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public final class StmtApplierTest {

	private static final VarDecl<IntType> X = Var("x", Int());
	private static final VarDecl<IntType> Y = Var("y", Int());

	private static final Tuple2<Decl<?>, LitExpr<?>> X_IS_1 = Tuple2.of(X, Int(1));
	private static final Tuple2<Decl<?>, LitExpr<?>> X_IS_2 = Tuple2.of(X, Int(2));
	private static final Tuple2<Decl<?>, LitExpr<?>> Y_IS_2 = Tuple2.of(Y, Int(2));

	private static final Stmt SKIP = Skip();
	private static final Stmt HAVOC_X = Havoc(X);
	private static final Stmt ASSUME_GT_X_0 = Assume(Gt(X.getRef(), Int(0)));
	private static final Stmt ASSUME_LEQ_X_0 = Assume(Leq(X.getRef(), Int(0)));
	private static final Stmt ASSUME_EQ_X_1 = Assume(Eq(X.getRef(), Int(1)));
	private static final Stmt ASSUME_LEQ_X_Y = Assume(Leq(X.getRef(), Y.getRef()));
	private static final Stmt ASSIGN_X_1 = Assign(X, Int(1));
	private static final Stmt ASSIGN_X_2 = Assign(X, Int(2));
	private static final Stmt ASSIGN_X_Y = Assign(X, Y.getRef());

	@Parameter(0)
	public Stmt stmt;

	@Parameter(1)
	public Set<Tuple2<Decl<?>, LitExpr<?>>> initialEntries;

	@Parameter(2)
	public boolean approximate;

	@Parameter(3)
	public ApplyResult expectedResult;

	@Parameter(4)
	public Set<Tuple2<Decl<?>, LitExpr<?>>> finalEntries;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{HAVOC_X, of(X_IS_1), false, SUCCESS, of()},

				{HAVOC_X, of(Y_IS_2), false, SUCCESS, of(Y_IS_2)},

				{HAVOC_X, of(X_IS_1, Y_IS_2), false, SUCCESS, of(Y_IS_2)},

				{HAVOC_X, of(), false, SUCCESS, of()},

				{ASSUME_GT_X_0, of(X_IS_1), false, SUCCESS, of(X_IS_1)},

				{ASSUME_GT_X_0, of(Y_IS_2), false, FAILURE, of(Y_IS_2)},

				{ASSUME_GT_X_0, of(X_IS_1, Y_IS_2), false, SUCCESS, of(X_IS_1, Y_IS_2)},

				{ASSUME_GT_X_0, of(), false, FAILURE, of()},

				{ASSUME_LEQ_X_0, of(X_IS_1), false, BOTTOM, of(X_IS_1)},

				{ASSUME_LEQ_X_0, of(Y_IS_2), false, FAILURE, of(Y_IS_2)},

				{ASSUME_LEQ_X_0, of(X_IS_1, Y_IS_2), false, BOTTOM, of(X_IS_1, Y_IS_2)},

				{ASSUME_LEQ_X_Y, of(X_IS_1), false, FAILURE, of(X_IS_1)},

				{ASSUME_LEQ_X_Y, of(Y_IS_2), false, FAILURE, of(Y_IS_2)},

				{ASSUME_LEQ_X_Y, of(X_IS_1, Y_IS_2), false, SUCCESS, of(X_IS_1, Y_IS_2)},

				{ASSUME_LEQ_X_Y, of(), false, FAILURE, of()},

				{ASSIGN_X_1, of(), false, SUCCESS, of(X_IS_1)},

				{ASSIGN_X_1, of(Y_IS_2), false, SUCCESS, of(X_IS_1, Y_IS_2)},

				{ASSIGN_X_1, of(X_IS_1, Y_IS_2), false, SUCCESS, of(X_IS_1, Y_IS_2)},

				{ASSIGN_X_2, of(), false, SUCCESS, of(X_IS_2)},

				{ASSIGN_X_2, of(X_IS_1), false, SUCCESS, of(X_IS_2)},

				{ASSIGN_X_Y, of(), false, FAILURE, of()},

				{ASSIGN_X_Y, of(X_IS_1), false, FAILURE, of(X_IS_1)},

				{ASSIGN_X_Y, of(X_IS_1), true, SUCCESS, of()},

				{ASSIGN_X_Y, of(X_IS_1, Y_IS_2), false, SUCCESS, of(X_IS_2, Y_IS_2)},

				{ASSIGN_X_Y, of(Y_IS_2), false, SUCCESS, of(X_IS_2, Y_IS_2)},

				{SKIP, of(X_IS_1), false, SUCCESS, of(X_IS_1)},

				{ASSUME_EQ_X_1, of(), false, SUCCESS, of(X_IS_1)},

		});
	}

	@Test
	public void test() {
		// Arrange
		final MutableValuation val = new MutableValuation();
		for (final Tuple2<Decl<?>, LitExpr<?>> entry : initialEntries) {
			val.put(entry.get1(), entry.get2());
		}

		// Act
		final ApplyResult actualResult = StmtApplier.apply(stmt, val, approximate);

		// Assert
		assertEquals(expectedResult, actualResult);
		assertEquals(finalEntries.size(), val.getDecls().size());
		for (final Tuple2<Decl<?>, LitExpr<?>> entry : finalEntries) {
			final LitExpr<?> lit = val.eval(entry.get1()).get();
			assertEquals(lit, entry.get2());
		}
	}

}
