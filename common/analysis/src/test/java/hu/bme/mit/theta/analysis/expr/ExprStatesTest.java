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
package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class ExprStatesTest {

	private final VarDecl<IntType> vx = Var("x", Int());
	private final ExplPrec prec = ExplPrec.of(Collections.singleton(vx));
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();

	@Test
	public void test1() {
		final Expr<BoolType> expr = Geq(vx.getRef(), Int(0));
		final VarIndexing idx = VarIndexing.all(0);

		Assert.assertEquals(1, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 1).size());
		Assert.assertEquals(5, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 5).size());
		Assert.assertEquals(10, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 10).size());
	}

	@Test
	public void test2() {
		final Expr<BoolType> expr = BoolExprs.And(Geq(vx.getRef(), Int(0)), Geq(Int(3), vx.getRef()));
		final VarIndexing idx = VarIndexing.all(0);

		Assert.assertEquals(2, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 2).size());
		Assert.assertEquals(4, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 4).size());
		Assert.assertEquals(4, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 10).size());
		Assert.assertEquals(4, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx, 0).size());
		Assert.assertEquals(4, ExprStates.createStatesForExpr(solver, expr, 0, prec::createState, idx).size());
	}
}
