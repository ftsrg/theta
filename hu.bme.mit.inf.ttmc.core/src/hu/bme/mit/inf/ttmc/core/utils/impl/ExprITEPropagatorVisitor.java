package hu.bme.mit.inf.ttmc.core.utils.impl;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

public class ExprITEPropagatorVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {
	private ExprVisitor<Void, Expr<? extends Type>> exprITEPusherVisitor;

	public ExprITEPropagatorVisitor(ConstraintManager manager, ExprVisitor<Void, Expr<? extends Type>> exprITEPusherVisitor) {
		this.exprITEPusherVisitor = exprITEPusherVisitor;
	}
	
	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(NullaryExpr<ExprType> expr, Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			UnaryExpr<OpType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr.withOp((Expr<? extends OpType>) expr.getOp().accept(this, param)).accept(exprITEPusherVisitor, param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr.withOps(
				(Expr<? extends LeftOpType>) expr.getLeftOp().accept(this, param),
				(Expr<? extends RightOpType>) expr.getRightOp().accept(this, param))
				.accept(exprITEPusherVisitor, param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (Expr<? extends OpsType> op : expr.getOps()) ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops).accept(exprITEPusherVisitor, param);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@SuppressWarnings("unchecked")
	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		// Apply propagation to operand(s)
		return expr.withOps(
				expr.getCond(),
				(Expr<? extends ExprType>) expr.getThen().accept(this, param),
				(Expr<? extends ExprType>) expr.getElse().accept(this, param));
	}

}
