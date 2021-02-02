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
package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class PredTransFuncTest {
	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());
	private final Solver solver = Z3SolverFactory.getInstance().createSolver();
	private final PredTransFunc transFunc = PredTransFunc.create(PredAbstractors.booleanSplitAbstractor(solver));

	@Test
	public void test1() {
		// (x<5) ---[x := x+1]--> (x<5)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Lt(x.getRef(), Int(5))));
		final PredState state = PredState.of(Lt(x.getRef(), Int(5)));
		final ExprAction action = new BasicStmtAction(Stmts.Assign(x, Add(x.getRef(), Int(1))));
		Assert.assertEquals(2, transFunc.getSuccStates(state, action, prec).size());
	}

	@Test
	public void test2() {
		// (x<4) ---[x := x+1]--> (x<5)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Lt(x.getRef(), Int(5))));
		final PredState state = PredState.of(Lt(x.getRef(), Int(4)));
		final ExprAction action = new BasicStmtAction(Stmts.Assign(x, Add(x.getRef(), Int(1))));
		Assert.assertEquals(1, transFunc.getSuccStates(state, action, prec).size());
	}

	@Test
	public void test3() {
		// (x>0) ---[x := x+y]--> (x>0, y>0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Gt(x.getRef(), Int(0)), Gt(y.getRef(), Int(0))));
		final PredState state = PredState.of(Gt(x.getRef(), Int(0)));
		final ExprAction action = new BasicStmtAction(Stmts.Assign(x, Add(x.getRef(), y.getRef())));
		Assert.assertEquals(3, transFunc.getSuccStates(state, action, prec).size());
	}

	@Test
	public void testBottom() {
		// (x>0) ---[assume x=0]--> (x>0)?
		final PredPrec prec = PredPrec.of(ImmutableList.of(Gt(x.getRef(), Int(0))));
		final PredState state = PredState.of(Gt(x.getRef(), Int(0)));
		final ExprAction action = new BasicStmtAction(Stmts.Assume(Eq(Int(0), x.getRef())));
		final Collection<? extends PredState> succStates = transFunc.getSuccStates(state, action, prec);
		Assert.assertEquals(1, succStates.size());
		Assert.assertEquals(PredState.bottom(), Utils.singleElementOf(succStates));
	}

	private static final class BasicStmtAction extends StmtAction {
		private final Stmt stmt;

		public BasicStmtAction(final Stmt stmt) {
			this.stmt = stmt;
		}

		@Override
		public List<Stmt> getStmts() {
			return Collections.singletonList(stmt);
		}
	}
}
