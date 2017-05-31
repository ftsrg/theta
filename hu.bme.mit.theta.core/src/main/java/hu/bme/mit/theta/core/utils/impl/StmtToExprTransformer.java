package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.expr.AbstractExprs.Eq;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

final class StmtToExprTransformer {

	private StmtToExprTransformer() {
	}

	public static UnfoldResult toExpr(final Stmt stmt, final VarIndexing indexing) {
		return stmt.accept(StmtToExprVisitor.INSTANCE, indexing);
	}

	public static UnfoldResult toExpr(final List<? extends Stmt> stmts, final VarIndexing indexing) {
		final Collection<Expr<? extends BoolType>> resultExprs = new ArrayList<>();
		VarIndexing resultIndexing = indexing;

		for (final Stmt stmt : stmts) {
			final UnfoldResult subResult = toExpr(stmt, resultIndexing);
			resultExprs.addAll(subResult.exprs);
			resultIndexing = subResult.indexing;
		}

		return UnfoldResult.of(resultExprs, resultIndexing);
	}

	////////

	private static class StmtToExprVisitor extends FailStmtVisitor<VarIndexing, UnfoldResult> {
		private static final StmtToExprVisitor INSTANCE = new StmtToExprVisitor();

		private StmtToExprVisitor() {
		}

		////////

		@Override
		public UnfoldResult visit(final AssumeStmt stmt, final VarIndexing indexing) {
			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<? extends BoolType> expr = ExprUtils.applyPrimes(cond, indexing);
			return UnfoldResult.of(ImmutableList.of(expr), indexing);
		}

		@Override
		public <DeclType extends Type> UnfoldResult visit(final HavocStmt<DeclType> stmt, final VarIndexing indexing) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final VarIndexing newIndexing = indexing.inc(varDecl);
			return UnfoldResult.of(ImmutableList.of(), newIndexing);
		}

		@Override
		public <DeclType extends Type> UnfoldResult visit(final AssignStmt<DeclType> stmt, final VarIndexing indexing) {
			final VarDecl<DeclType> varDecl = stmt.getVarDecl();
			final VarIndexing newIndexing = indexing.inc(varDecl);
			final Expr<DeclType> rhs = ExprUtils.applyPrimes(stmt.getExpr(), indexing);
			final Expr<DeclType> lhs = ExprUtils.applyPrimes(varDecl.getRef(), newIndexing);

			final Expr<BoolType> expr = Eq(lhs, rhs);
			return UnfoldResult.of(ImmutableList.of(expr), newIndexing);
		}
	}

}
