package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.utils.impl.PrimeApplier.applyPrimes;

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

	public static StmtToExprResult toExpr(final Stmt stmt, final VarIndexes indexes) {
		return stmt.accept(StmtToExprVisitor.INSTANCE, indexes);
	}

	public static StmtToExprResult toExpr(final List<? extends Stmt> stmts, final VarIndexes indexes) {
		final Collection<Expr<? extends BoolType>> resultExprs = new ArrayList<>();
		VarIndexes resultIndexes = indexes;

		for (final Stmt stmt : stmts) {
			final StmtToExprResult subResult = toExpr(stmt, resultIndexes);
			resultExprs.addAll(subResult.exprs);
			resultIndexes = subResult.indexes;
		}

		return StmtToExprResult.of(resultExprs, resultIndexes);
	}

	////////

	private static class StmtToExprVisitor extends FailStmtVisitor<VarIndexes, StmtToExprResult> {
		private static final StmtToExprVisitor INSTANCE = new StmtToExprVisitor();

		private StmtToExprVisitor() {
		}

		////////

		@Override
		public StmtToExprResult visit(final AssumeStmt stmt, final VarIndexes indexes) {
			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<? extends BoolType> expr = applyPrimes(cond, indexes);
			return StmtToExprResult.of(ImmutableList.of(expr), indexes);
		}

		@Override
		public <DeclType extends Type> StmtToExprResult visit(final HavocStmt<DeclType> stmt,
				final VarIndexes indexes) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final VarIndexes newIndexMap = indexes.inc(varDecl);
			return StmtToExprResult.of(ImmutableList.of(), newIndexMap);
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> StmtToExprResult visit(
				final AssignStmt<DeclType, ExprType> stmt, final VarIndexes indexes) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final VarIndexes newIndexes = indexes.inc(varDecl);
			final Expr<?> rhs = applyPrimes(stmt.getExpr(), indexes);
			final Expr<?> lhs = applyPrimes(varDecl.getRef(), newIndexes);

			final Expr<? extends BoolType> expr = Exprs.Eq(lhs, rhs);
			return StmtToExprResult.of(ImmutableList.of(expr), newIndexes);
		}
	}

}
