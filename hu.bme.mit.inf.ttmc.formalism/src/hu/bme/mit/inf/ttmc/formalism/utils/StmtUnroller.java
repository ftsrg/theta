package hu.bme.mit.inf.ttmc.formalism.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class StmtUnroller {

	private static final StmtToExprVisitor VISITOR;

	static {
		VISITOR = new StmtToExprVisitor();
	}

	private StmtUnroller() {
	}

	public static StmtToExprResult transform(final Stmt stmt, final VarIndexes indexes) {
		return stmt.accept(VISITOR, indexes);
	}

	public static StmtToExprResult transform(final List<? extends Stmt> stmts, final VarIndexes indexes) {
		final Collection<Expr<? extends BoolType>> resultExprs = new ArrayList<>();
		VarIndexes resultIndexes = indexes;

		for (final Stmt stmt : stmts) {
			final StmtToExprResult subResult = transform(stmt, resultIndexes);
			resultExprs.addAll(subResult.exprs);
			resultIndexes = subResult.indexes;
		}

		return StmtToExprResult.of(resultExprs, resultIndexes);
	}

	////////

	public static class StmtToExprResult {
		final Collection<Expr<? extends BoolType>> exprs;
		final VarIndexes indexes;

		private StmtToExprResult(final Collection<? extends Expr<? extends BoolType>> exprs, final VarIndexes indexes) {
			this.exprs = ImmutableList.copyOf(exprs);
			this.indexes = indexes;
		}

		private static StmtToExprResult of(final Collection<? extends Expr<? extends BoolType>> exprs,
				final VarIndexes indexes) {
			return new StmtToExprResult(exprs, indexes);
		}

		public Collection<? extends Expr<? extends BoolType>> getExprs() {
			return exprs;
		}

		public VarIndexes getIndexes() {
			return indexes;
		}
	}

	////////

	private static class StmtToExprVisitor extends FailStmtVisitor<VarIndexes, StmtToExprResult> {

		private StmtToExprVisitor() {
		}

		////////

		@Override
		public StmtToExprResult visit(final AssumeStmt stmt, final VarIndexes indexes) {
			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<? extends BoolType> expr = VarToConstRewriter.rewrite(cond, indexes);
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
			final Expr<?> rhs = VarToConstRewriter.rewrite(stmt.getExpr(), indexes);
			final Expr<?> lhs = VarToConstRewriter.rewrite(varDecl.getRef(), newIndexes);

			final Expr<? extends BoolType> expr = Exprs.Eq(lhs, rhs);
			return StmtToExprResult.of(ImmutableList.of(expr), newIndexes);
		}

	}

}
