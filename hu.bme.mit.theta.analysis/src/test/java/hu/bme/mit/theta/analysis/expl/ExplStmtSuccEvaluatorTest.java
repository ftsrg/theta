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

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.expl.ExplStmtSuccEvaluator.EvalResult;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplStmtSuccEvaluatorTest {

	VarDecl<IntType> X = Decls.Var("x", Int());
	VarDecl<IntType> Y = Decls.Var("y", Int());

	ExplState sb = ExplState.createBottom();
	ExplState sx = ExplState.create(ImmutableValuation.builder().put(X, Int(1)).build());
	ExplState sy = ExplState.create(ImmutableValuation.builder().put(Y, Int(2)).build());
	ExplState sxy = ExplState.create(ImmutableValuation.builder().put(X, Int(1)).put(Y, Int(2)).build());
	ExplState st = ExplState.createTop();

	@Test
	public void testVisitorHavoc() {
		final Stmt havoc = Stmts.Havoc(X);

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, havoc));
		Assert.assertEquals(EvalResult.precise(st), ExplStmtSuccEvaluator.evalSucc(sx, havoc));
		Assert.assertEquals(EvalResult.precise(sy), ExplStmtSuccEvaluator.evalSucc(sy, havoc));
		Assert.assertEquals(EvalResult.precise(sy), ExplStmtSuccEvaluator.evalSucc(sxy, havoc));
		Assert.assertEquals(EvalResult.precise(st), ExplStmtSuccEvaluator.evalSucc(st, havoc));
	}

	@Test
	public void testVisitorAssume() {
		final Stmt assume1 = Stmts.Assume(IntExprs.Gt(X.getRef(), Int(0)));
		final Stmt assume2 = Stmts.Assume(IntExprs.Leq(X.getRef(), Int(0)));
		final Stmt assume3 = Stmts.Assume(IntExprs.Leq(X.getRef(), Y.getRef()));

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assume1));
		Assert.assertEquals(EvalResult.precise(sx), ExplStmtSuccEvaluator.evalSucc(sx, assume1));
		Assert.assertEquals(EvalResult.imprecise(sy), ExplStmtSuccEvaluator.evalSucc(sy, assume1));
		Assert.assertEquals(EvalResult.precise(sxy), ExplStmtSuccEvaluator.evalSucc(sxy, assume1));
		Assert.assertEquals(EvalResult.imprecise(st), ExplStmtSuccEvaluator.evalSucc(st, assume1));

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assume2));
		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sx, assume2));
		Assert.assertEquals(EvalResult.imprecise(sy), ExplStmtSuccEvaluator.evalSucc(sy, assume2));
		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sxy, assume2));
		Assert.assertEquals(EvalResult.imprecise(st), ExplStmtSuccEvaluator.evalSucc(st, assume2));

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assume3));
		Assert.assertEquals(EvalResult.imprecise(sx), ExplStmtSuccEvaluator.evalSucc(sx, assume3));
		Assert.assertEquals(EvalResult.imprecise(sy), ExplStmtSuccEvaluator.evalSucc(sy, assume3));
		Assert.assertEquals(EvalResult.precise(sxy), ExplStmtSuccEvaluator.evalSucc(sxy, assume3));
		Assert.assertEquals(EvalResult.imprecise(st), ExplStmtSuccEvaluator.evalSucc(st, assume3));
	}

	@Test
	public void testVisitorAssign() {
		final Stmt assign1 = Stmts.Assign(X, Int(1));
		final Stmt assign2 = Stmts.Assign(X, Int(2));
		final Stmt assign3 = Stmts.Assign(X, Y.getRef());
		final ExplState sx2 = ExplState.create(ImmutableValuation.builder().put(X, Int(2)).build());
		final ExplState sxy2 = ExplState.create(ImmutableValuation.builder().put(X, Int(2)).put(Y, Int(2)).build());

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assign1));
		Assert.assertEquals(EvalResult.precise(sx), ExplStmtSuccEvaluator.evalSucc(st, assign1));
		Assert.assertEquals(EvalResult.precise(sxy), ExplStmtSuccEvaluator.evalSucc(sy, assign1));
		Assert.assertEquals(EvalResult.precise(sxy), ExplStmtSuccEvaluator.evalSucc(sxy, assign1));

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assign2));
		Assert.assertEquals(EvalResult.precise(sx2), ExplStmtSuccEvaluator.evalSucc(sx, assign2));
		Assert.assertEquals(EvalResult.precise(sx2), ExplStmtSuccEvaluator.evalSucc(st, assign2));

		Assert.assertEquals(EvalResult.precise(sb), ExplStmtSuccEvaluator.evalSucc(sb, assign3));
		Assert.assertEquals(EvalResult.imprecise(st), ExplStmtSuccEvaluator.evalSucc(sx, assign3));
		Assert.assertEquals(EvalResult.precise(sxy2), ExplStmtSuccEvaluator.evalSucc(sxy, assign3));
		Assert.assertEquals(EvalResult.precise(sxy2), ExplStmtSuccEvaluator.evalSucc(sy, assign3));
		Assert.assertEquals(EvalResult.imprecise(st), ExplStmtSuccEvaluator.evalSucc(st, assign3));
	}
}
