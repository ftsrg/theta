package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.theta.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.formalism.utils.FailStmtVisitor;

public class StmtToExprTransformer {

	private final StmtToExprVisitor visitor;

	public StmtToExprTransformer(final VarMap varMap) {
		visitor = new StmtToExprVisitor(varMap);
	}

	public StmtToExprResult transform(final Stmt stmt, final IndexMap indexMap) {
		return stmt.accept(visitor, indexMap);
	}

	////////

	public static class StmtToExprResult {
		final Collection<Expr<? extends BoolType>> exprs;
		final IndexMap indexMap;

		private StmtToExprResult(final Collection<? extends Expr<? extends BoolType>> exprs, final IndexMap indexMap) {
			this.exprs = ImmutableList.copyOf(exprs);
			this.indexMap = indexMap;
		}

		private static StmtToExprResult of(final Collection<? extends Expr<? extends BoolType>> exprs,
				final IndexMap indexMap) {
			return new StmtToExprResult(exprs, indexMap);
		}

		public Collection<? extends Expr<? extends BoolType>> getExprs() {
			return exprs;
		}

		public IndexMap getIndexMap() {
			return indexMap;
		}
	}

	////////

	private static class StmtToExprVisitor extends FailStmtVisitor<IndexMap, StmtToExprResult> {

		private final VarToConstRewriter varToConst;

		private StmtToExprVisitor(final VarMap varMap) {
			varToConst = new VarToConstRewriter(varMap);
		}

		////////

		@Override
		public StmtToExprResult visit(final AssumeStmt stmt, final IndexMap indexMap) {
			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<? extends BoolType> expr = varToConst.rewrite(cond, indexMap);
			return StmtToExprResult.of(ImmutableList.of(expr), indexMap);
		}

		@Override
		public <DeclType extends Type> StmtToExprResult visit(final HavocStmt<DeclType> stmt, final IndexMap indexMap) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final IndexMap newIndexMap = indexMap.inc(varDecl);
			return StmtToExprResult.of(ImmutableList.of(), newIndexMap);
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> StmtToExprResult visit(
				final AssignStmt<DeclType, ExprType> stmt, final IndexMap indexMap) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			final IndexMap newIndexMap = indexMap.inc(varDecl);
			final Expr<?> rhs = varToConst.rewrite(stmt.getExpr(), indexMap);
			final Expr<?> lhs = varToConst.rewrite(varDecl.getRef(), newIndexMap);

			final Expr<? extends BoolType> expr = Exprs.Eq(lhs, rhs);
			return StmtToExprResult.of(ImmutableList.of(expr), newIndexMap);
		}

	}

}