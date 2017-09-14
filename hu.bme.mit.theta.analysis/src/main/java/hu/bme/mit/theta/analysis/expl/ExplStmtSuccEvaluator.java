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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.FailStmtVisitor;

public class ExplStmtSuccEvaluator {

	public static final EvaluatorVisitor visitor = new EvaluatorVisitor();

	public static EvalResult evalSucc(final ExplState state, final Stmt stmt) {
		return stmt.accept(visitor, state);
	}

	public static final class EvalResult {
		private final ExplState state;
		private final boolean isPrecise;

		private EvalResult(final ExplState state, final boolean isPrecise) {
			this.state = state;
			this.isPrecise = isPrecise;
		}

		public static EvalResult precise(final ExplState state) {
			return new EvalResult(state, true);
		}

		public static EvalResult imprecise(final ExplState state) {
			return new EvalResult(state, false);
		}

		public ExplState getState() {
			return state;
		}

		public boolean isPrecise() {
			return isPrecise;
		}

		@Override
		public boolean equals(final Object obj) {
			if (obj instanceof EvalResult) {
				final EvalResult that = (EvalResult) obj;
				return this.isPrecise == that.isPrecise && this.state.equals(that.state);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return state.hashCode() * Boolean.hashCode(isPrecise);
		}
	}

	private static final class EvaluatorVisitor extends FailStmtVisitor<ExplState, EvalResult> {

		@Override
		public <DeclType extends Type> EvalResult visit(final AssignStmt<DeclType> stmt, final ExplState param) {
			if (param.isBottom()) {
				return EvalResult.precise(param);
			}

			final VarDecl<DeclType> varDecl = stmt.getVarDecl();
			final Expr<DeclType> exprSimplified = ExprUtils.simplify(stmt.getExpr(), param);
			if (exprSimplified instanceof LitExpr<?>) {
				final LitExpr<DeclType> lit = (LitExpr<DeclType>) exprSimplified;
				final MutableValuation mutableVal = MutableValuation.copyOf(param).remove(varDecl).put(varDecl, lit);
				final BasicValuation basicVal = BasicValuation.copyOf(mutableVal);
				return EvalResult.precise(ExplState.create(basicVal));
			} else {
				final MutableValuation mutableVal = MutableValuation.copyOf(param).remove(varDecl);
				final BasicValuation basicVal = BasicValuation.copyOf(mutableVal);
				return EvalResult.imprecise(ExplState.create(basicVal));
			}
		}

		@Override
		public EvalResult visit(final AssumeStmt stmt, final ExplState param) {
			if (param.isBottom()) {
				return EvalResult.precise(param);
			}

			final Expr<BoolType> condSimplified = ExprUtils.simplify(stmt.getCond(), param);
			if (condSimplified instanceof BoolLitExpr) {
				if (condSimplified.equals(BoolExprs.True())) {
					return EvalResult.precise(param);
				} else {
					return EvalResult.precise(ExplState.createBottom());
				}
			} else {
				return EvalResult.imprecise(param);
			}
		}

		@Override
		public <LhsType extends Type> EvalResult visit(final HavocStmt<LhsType> stmt, final ExplState param) {
			final VarDecl<LhsType> varToHavoc = stmt.getVarDecl();
			if (param.getDecls().contains(varToHavoc)) {
				final MutableValuation mutableVal = MutableValuation.copyOf(param).remove(varToHavoc);
				final BasicValuation basicVal = BasicValuation.copyOf(mutableVal);
				return EvalResult.precise(ExplState.create(basicVal));
			} else {
				return EvalResult.precise(param);
			}
		}
	}
}
