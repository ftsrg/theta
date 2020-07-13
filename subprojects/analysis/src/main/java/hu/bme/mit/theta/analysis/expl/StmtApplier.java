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
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

final class StmtApplier {

	public static enum ApplyResult {
		FAILURE, SUCCESS, BOTTOM
	}

	private StmtApplier() {
	}

	public static ApplyResult apply(final Stmt stmt, final MutableValuation val, final boolean approximate) {
		if (stmt instanceof AssignStmt) {
			final AssignStmt<?> assignStmt = (AssignStmt<?>) stmt;
			return applyAssign(assignStmt, val, approximate);
		} else if (stmt instanceof AssumeStmt) {
			final AssumeStmt assumeStmt = (AssumeStmt) stmt;
			return applyAssume(assumeStmt, val, approximate);
		} else if (stmt instanceof HavocStmt) {
			final HavocStmt<?> havocStmt = (HavocStmt<?>) stmt;
			return applyHavoc(havocStmt, val, approximate);
		} else if (stmt instanceof SkipStmt) {
			final SkipStmt skipStmt = (SkipStmt) stmt;
			return applySkip(skipStmt);
		} else {
			throw new UnsupportedOperationException("Unhandled statement: " + stmt);
		}
	}

	private static ApplyResult applyAssign(final AssignStmt<?> stmt, final MutableValuation val,
										   final boolean approximate) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		final Expr<?> expr = ExprUtils.simplify(stmt.getExpr(), val);
		if (expr instanceof LitExpr<?>) {
			final LitExpr<?> lit = (LitExpr<?>) expr;
			val.put(varDecl, lit);
			return ApplyResult.SUCCESS;
		} else if (approximate) {
			val.remove(varDecl);
			return ApplyResult.SUCCESS;
		} else {
			return ApplyResult.FAILURE;
		}
	}

	private static ApplyResult applyAssume(final AssumeStmt stmt, final MutableValuation val,
										   final boolean approximate) {
		final Expr<BoolType> cond = ExprUtils.simplify(stmt.getCond(), val);
		if (cond instanceof BoolLitExpr) {
			final BoolLitExpr condLit = (BoolLitExpr) cond;
			if (condLit.getValue()) {
				return ApplyResult.SUCCESS;
			} else {
				return ApplyResult.BOTTOM;
			}
		} else if (checkAssumeVarEqualsLit(cond, val)) {
			return ApplyResult.SUCCESS;
		} else {
			if (approximate) {
				return ApplyResult.SUCCESS;
			} else {
				return ApplyResult.FAILURE;
			}
		}
	}

	// Helper function to evaluate assumptions of form [x = 1] or [not x != 1]
	private static boolean checkAssumeVarEqualsLit(final Expr<BoolType> cond, final MutableValuation val) {
		RefExpr<?> ref = null;
		LitExpr<?> lit = null;

		if (cond instanceof EqExpr<?>) {
			final EqExpr<?> condEq = (EqExpr<?>) cond;

			if (condEq.getLeftOp() instanceof RefExpr<?> && condEq.getRightOp() instanceof LitExpr<?>) {
				ref = (RefExpr<?>) condEq.getLeftOp();
				lit = (LitExpr<?>) condEq.getRightOp();
			}

			if (condEq.getRightOp() instanceof RefExpr<?> && condEq.getLeftOp() instanceof LitExpr<?>) {
				ref = (RefExpr<?>) condEq.getRightOp();
				lit = (LitExpr<?>) condEq.getLeftOp();
			}
		}

		if (cond instanceof NotExpr) {
			final NotExpr condNE = (NotExpr) cond;
			if (condNE.getOp() instanceof NeqExpr<?>) {
				final NeqExpr<?> condNeq = (NeqExpr<?>) condNE.getOp();

				if (condNeq.getLeftOp() instanceof RefExpr<?> && condNeq.getRightOp() instanceof LitExpr<?>) {
					ref = (RefExpr<?>) condNeq.getLeftOp();
					lit = (LitExpr<?>) condNeq.getRightOp();
				}

				if (condNeq.getRightOp() instanceof RefExpr<?> && condNeq.getLeftOp() instanceof LitExpr<?>) {
					ref = (RefExpr<?>) condNeq.getRightOp();
					lit = (LitExpr<?>) condNeq.getLeftOp();
				}
			}
		}

		if (ref != null && lit != null){
			val.put(ref.getDecl(), lit);
			return true;
		}

		return false;
	}

	private static ApplyResult applyHavoc(final HavocStmt<?> stmt, final MutableValuation val,
										  final boolean approximate) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		val.remove(varDecl);
		return ApplyResult.SUCCESS;
	}

	private static ApplyResult applySkip(final SkipStmt skipStmt) {
		return ApplyResult.SUCCESS;
	}

}
