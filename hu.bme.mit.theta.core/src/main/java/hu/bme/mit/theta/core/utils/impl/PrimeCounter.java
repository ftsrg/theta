package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.QuantifiedExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.utils.impl.VarIndexing.Builder;

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
		public <DeclType extends Type> VarIndexing.Builder visit(final RefExpr<DeclType> expr, final Integer nPrimes) {
			final Decl<DeclType> decl = expr.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<DeclType> var = (VarDecl<DeclType>) decl;
				return VarIndexing.builder(0).inc(var, nPrimes);
			} else {
				return VarIndexing.builder(0);
			}
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
		protected <OpsType extends Type, ExprType extends Type> Builder visitQuantified(final QuantifiedExpr expr,
				final Integer param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
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