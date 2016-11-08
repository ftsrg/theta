package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;

final class PrimeCounter {

	private static final PrimeCounterVisitor VISITOR = new PrimeCounterVisitor();

	private PrimeCounter() {
	}

	public static VarIndexing countPrimes(final Expr<?> expr) {
		return expr.accept(VISITOR, 0).build();
	}

	private static final class PrimeCounterVisitor extends ArityBasedExprVisitor<Integer, VarIndexing.Builder> {

		private PrimeCounterVisitor() {
		}

		@Override
		public <DeclType extends Type> VarIndexing.Builder visit(final VarRefExpr<DeclType> expr,
				final Integer nPrimes) {
			return VarIndexing.builder(0).inc(expr.getDecl(), nPrimes);

		}

		@Override
		public <ExprType extends Type> VarIndexing.Builder visit(final PrimedExpr<ExprType> expr,
				final Integer nPrimes) {
			return expr.getOp().accept(this, nPrimes + 1);
		}

		////

		@Override
		protected <ExprType extends Type> VarIndexing.Builder visitNullary(final NullaryExpr<ExprType> expr,
				final Integer nPrimes) {
			return VarIndexing.builder(0);
		}

		@Override
		protected <OpType extends Type, ExprType extends Type> VarIndexing.Builder visitUnary(
				final UnaryExpr<OpType, ExprType> expr, final Integer nPrimes) {
			return expr.getOp().accept(this, nPrimes);
		}

		@Override
		protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> VarIndexing.Builder visitBinary(
				final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Integer nPrimes) {
			final VarIndexing.Builder leftBuilder = expr.getLeftOp().accept(this, nPrimes);
			final VarIndexing.Builder righBuilder = expr.getRightOp().accept(this, nPrimes);
			return leftBuilder.join(righBuilder);
		}

		@Override
		protected <OpsType extends Type, ExprType extends Type> VarIndexing.Builder visitMultiary(
				final MultiaryExpr<OpsType, ExprType> expr, final Integer nPrimes) {
			return expr.getOps().stream().map(e -> e.accept(this, nPrimes)).reduce(VarIndexing.builder(0),
					VarIndexing.Builder::join);
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> VarIndexing.Builder visit(
				final ArrayReadExpr<IndexType, ElemType> expr, final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> VarIndexing.Builder visit(
				final ArrayWriteExpr<IndexType, ElemType> expr, final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> VarIndexing.Builder visit(
				final FuncLitExpr<ParamType, ResultType> expr, final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> VarIndexing.Builder visit(
				final FuncAppExpr<ParamType, ResultType> expr, final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ReturnType extends Type> VarIndexing.Builder visit(final ProcCallExpr<ReturnType> expr,
				final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ExprType extends Type> VarIndexing.Builder visit(final IteExpr<ExprType> expr, final Integer nPrimes) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

	}

}