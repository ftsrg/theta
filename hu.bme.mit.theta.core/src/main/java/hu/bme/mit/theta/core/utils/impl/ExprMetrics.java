package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class ExprMetrics {

	private ExprMetrics() {
	}

	public interface ExprMetric extends ExprVisitor<Void, Integer> {
	}

	public static ExprMetric absoluteSize() {
		return new AbsoluteSizeVisitor();
	}

	/////

	private final static class AbsoluteSizeVisitor extends ArityBasedExprVisitor<Void, Integer> implements ExprMetric {

		@Override
		protected <ExprType extends Type> Integer visitNullary(final NullaryExpr<ExprType> expr, final Void param) {
			return 1;
		}

		@Override
		protected <OpType extends Type, ExprType extends Type> Integer visitUnary(
				final UnaryExpr<OpType, ExprType> expr, final Void param) {
			return 1 + expr.getOp().accept(this, null);
		}

		@Override
		protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Integer visitBinary(
				final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Void param) {
			return 1 + expr.getLeftOp().accept(this, null) + expr.getRightOp().accept(this, null);
		}

		@Override
		protected <OpsType extends Type, ExprType extends Type> Integer visitMultiary(
				final MultiaryExpr<OpsType, ExprType> expr, final Void param) {
			if (expr.getOps().size() == 0) {
				return 0;
			} else {
				return expr.getOps().size() - 1 + expr.getOps().stream().mapToInt(e -> e.accept(this, null)).sum();
			}
		}

		@Override
		protected <OpsType extends Type, ExprType extends Type> Integer visitQuantified(final QuantifiedExpr expr,
				final Void param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Integer visit(
				final ArrayReadExpr<IndexType, ElemType> expr, final Void param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Integer visit(
				final ArrayWriteExpr<IndexType, ElemType> expr, final Void param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Integer visit(
				final FuncLitExpr<ParamType, ResultType> expr, final Void param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Integer visit(
				final FuncAppExpr<ParamType, ResultType> expr, final Void param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <ReturnType extends Type> Integer visit(final ProcCallExpr<ReturnType> expr, final Void param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <ExprType extends Type> Integer visit(final IteExpr<ExprType> expr, final Void param) {
			return 1 + expr.getCond().accept(this, null) + expr.getThen().accept(this, null)
					+ expr.getElse().accept(this, null);
		}

	}
}
