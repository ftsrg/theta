package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
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
		} else {
			throw new AssertionError();
		}
	}

	private static ApplyResult applyAssign(final AssignStmt<?> stmt, final MutableValuation val,
			final boolean approximate) {
		final VarDecl<?> var = stmt.getVarDecl();
		final Expr<?> expr = ExprUtils.simplify(stmt.getExpr(), val);
		if (expr instanceof LitExpr<?>) {
			final LitExpr<?> lit = (LitExpr<?>) expr;
			val.put(var, lit);
			return ApplyResult.SUCCESS;
		} else if (approximate) {
			val.remove(var);
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
		} else {
			if (approximate) {
				return ApplyResult.SUCCESS;
			} else {
				return ApplyResult.FAILURE;
			}
		}
	}

	private static ApplyResult applyHavoc(final HavocStmt<?> stmt, final MutableValuation val,
			final boolean approximate) {
		final VarDecl<?> var = stmt.getVarDecl();
		val.remove(var);
		return ApplyResult.SUCCESS;
	}

}
