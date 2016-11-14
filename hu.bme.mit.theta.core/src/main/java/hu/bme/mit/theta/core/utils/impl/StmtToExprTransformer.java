package hu.bme.mit.theta.core.utils.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

final class StmtToExprTransformer {

	private StmtToExprTransformer() {
	}

	public static StmtToExprResult toExpr(final Stmt stmt, final VarIndexing indexing) {
		return stmt.accept(StmtToExprVisitor.INSTANCE, indexing);
	}

	public static StmtToExprResult toExpr(final List<? extends Stmt> stmts, final VarIndexing indexing) {
		final Collection<Expr<? extends BoolType>> resultExprs = new ArrayList<>();
		VarIndexing resultIndexing = indexing;

		for (final Stmt stmt : stmts) {
			final StmtToExprResult subResult = toExpr(stmt, resultIndexing);
			resultExprs.addAll(subResult.exprs);
			resultIndexing = subResult.indexing;
		}

		return StmtToExprResult.of(resultExprs, resultIndexing);
	}

	////////

	private static class StmtToExprVisitor extends FailStmtVisitor<VarIndexing, StmtToExprResult> {
		private static final StmtToExprVisitor INSTANCE = new StmtToExprVisitor();

		private StmtToExprVisitor() {
		}

		////////

		@Override
		public StmtToExprResult visit(final AssumeStmt stmt, final VarIndexing indexing) {
			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<? extends BoolType> expr = ExprUtils.applyPrimes(cond, indexing);
			return StmtToExprResult.of(ImmutableList.of(expr), indexing);
		}

		@Override
		public <DeclType extends Type> StmtToExprResult visit(final HavocStmt<DeclType> stmt,
				final VarIndexing indexing) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final VarIndexing newIndexing = indexing.inc(varDecl);
			return StmtToExprResult.of(ImmutableList.of(), newIndexing);
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> StmtToExprResult visit(
				final AssignStmt<DeclType, ExprType> stmt, final VarIndexing indexing) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final VarIndexing newIndexing = indexing.inc(varDecl);
			final Expr<?> rhs = ExprUtils.applyPrimes(stmt.getExpr(), indexing);
			final Expr<?> lhs = ExprUtils.applyPrimes(varDecl.getRef(), newIndexing);

			final Expr<? extends BoolType> expr = Exprs.Eq(lhs, rhs);
			return StmtToExprResult.of(ImmutableList.of(expr), newIndexing);
		}
	}

}
