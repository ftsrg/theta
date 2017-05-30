package hu.bme.mit.theta.core.utils.impl;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.proctype.ProcCallExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public class ItePropagatorVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {
	private final ExprVisitor<Void, Expr<? extends Type>> exprITEPusherVisitor;

	public ItePropagatorVisitor(final ExprVisitor<Void, Expr<? extends Type>> exprITEPusherVisitor) {
		this.exprITEPusherVisitor = exprITEPusherVisitor;
	}

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(final NullaryExpr<ExprType> expr,
			final Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			final UnaryExpr<OpType, ExprType> expr, final Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr.withOp((Expr<? extends OpType>) expr.getOp().accept(this, param)).accept(exprITEPusherVisitor,
				param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr
				.withOps((Expr<? extends LeftOpType>) expr.getLeftOp().accept(this, param),
						(Expr<? extends RightOpType>) expr.getRightOp().accept(this, param))
				.accept(exprITEPusherVisitor, param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			final MultiaryExpr<OpsType, ExprType> expr, final Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		final List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (final Expr<? extends OpsType> op : expr.getOps())
			ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops).accept(exprITEPusherVisitor, param);
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitQuantified(
			final QuantifiedExpr expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			final ArrayReadExpr<IndexType, ElemType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			final ArrayWriteExpr<IndexType, ElemType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			final FuncLitExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			final FuncAppExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcCallExpr<ReturnType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@SuppressWarnings("unchecked")
	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(final IteExpr<ExprType> expr, final Void param) {
		// Apply propagation to operand(s)
		return expr.withOps(expr.getCond(), (Expr<? extends ExprType>) expr.getThen().accept(this, param),
				(Expr<? extends ExprType>) expr.getElse().accept(this, param));
	}

}
