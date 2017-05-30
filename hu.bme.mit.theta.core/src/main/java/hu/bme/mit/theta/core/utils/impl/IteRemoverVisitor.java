package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.QuantifiedExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;

public class IteRemoverVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(final NullaryExpr<ExprType> expr,
			final Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			final UnaryExpr<OpType, ExprType> expr, final Void param) {
		return expr.withOp((Expr<? extends OpType>) expr.getOp().accept(this, param));
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Void param) {
		return expr.withOps((Expr<? extends LeftOpType>) expr.getLeftOp().accept(this, param),
				(Expr<? extends RightOpType>) expr.getRightOp().accept(this, param));
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			final MultiaryExpr<OpsType, ExprType> expr, final Void param) {
		final List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (final Expr<? extends OpsType> op : expr.getOps())
			ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops);
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
		// Apply ite(C,T,E) <=> (!C or T) and (C or E) transformation
		final Expr<? extends BoolType> cond = (Expr<? extends BoolType>) expr.getCond().accept(this, param);
		final Expr<? extends Type> then = expr.getThen().accept(this, param);
		final Expr<? extends Type> elze = expr.getElse().accept(this, param);
		return And(Or(Not(cond), (Expr<? extends BoolType>) then), Or(cond, (Expr<? extends BoolType>) elze));
	}

}
