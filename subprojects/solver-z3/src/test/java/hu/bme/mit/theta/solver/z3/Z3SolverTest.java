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
package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;

import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;

import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.Test;

import java.util.Optional;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public final class Z3SolverTest {

	@Test
	public void testSimple() {
		final Solver solver = Z3SolverFactory.getInstance().createSolver();

		// Create two integer constants x and y
		final ConstDecl<IntType> cx = Const("x", Int());
		final ConstDecl<IntType> cy = Const("y", Int());

		// Add x == y + 1 to the solver
		solver.add(Eq(cx.getRef(), Add(cy.getRef(), Int(1))));

		// Check, the expression should be satisfiable
		SolverStatus status = solver.check();
		assertTrue(status.isSat());

		// Add x < y to the solver
		solver.add(Lt(cx.getRef(), cy.getRef()));

		// Check, the expression should be unsatisfiable
		status = solver.check();
		assertTrue(status.isUnsat());
	}

	@Test
	public void testTrack() {
		final Solver solver = Z3SolverFactory.getInstance().createSolver();

		final ConstDecl<BoolType> ca = Const("a", Bool());
		final Expr<BoolType> expr = And(ca.getRef(), True());

		solver.push();
		solver.track(expr);

		final SolverStatus status = solver.check();

		assertTrue(status.isSat());

		final Valuation model = solver.getModel();

		assertNotNull(model);

		solver.pop();
	}

	@Test
	public void testFunc() {
		// Arrange
		final Solver solver = Z3SolverFactory.getInstance().createSolver();
		final ConstDecl<FuncType<IntType, IntType>> ca = Const("a", Func(Int(), Int()));
		final Expr<FuncType<IntType, IntType>> a = ca.getRef();
		final ParamDecl<IntType> px = Param("x", Int());
		final Expr<IntType> x = px.getRef();

		solver.add(Forall(of(px), Imply(Leq(x, Int(0)), Eq(App(a, x), Int(0)))));
		solver.add(Forall(of(px), Imply(Geq(x, Int(1)), Eq(App(a, x), Int(1)))));

		// Act
		final SolverStatus status = solver.check();
		assertTrue(status.isSat());
		final Valuation model = solver.getModel();
		final Optional<LitExpr<FuncType<IntType, IntType>>> optVal = model.eval(ca);
		final Expr<FuncType<IntType, IntType>> val = optVal.get();

		// Assert
		assertEquals(ca.getType(), val.getType());
	}
	
	@Test
	public void testArray() {
		final Solver solver = Z3SolverFactory.getInstance().createSolver();

        final ConstDecl<ArrayType<IntType, IntType>> arr = Const("arr", Array(Int(), Int()));

        solver.add(ArrayExprs.Eq(Write(arr.getRef(), Int(0), Int(1)), arr.getRef()));
        solver.add(ArrayExprs.Eq(Write(arr.getRef(), Int(1), Int(2)), arr.getRef()));

        // Check, the expression should be satisfiable
        SolverStatus status = solver.check();
        assertTrue(status.isSat());
        
        Valuation valuation = solver.getModel();
        final Optional<LitExpr<ArrayType<IntType, IntType>>> optVal = valuation.eval(arr);
		final Expr<ArrayType<IntType, IntType>> val = optVal.get();
		assertTrue(val instanceof ArrayLitExpr);
		var valLit = (ArrayLitExpr<IntType, IntType>)val;
		assertEquals(2, valLit.getElements().size());
		assertEquals(Int(1), Read(valLit, Int(0)).eval(ImmutableValuation.empty()));
		assertEquals(Int(2), Read(valLit, Int(1)).eval(ImmutableValuation.empty()));
	}

}
