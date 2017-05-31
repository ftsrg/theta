package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import com.google.common.collect.Collections2;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.proctype.ProcCallExpr;

public class ExprRewriterVisitor<P> extends ArityBasedExprVisitor<P, Expr<?>> {

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<ResultType> visit(
			final FuncAppExpr<ParamType, ResultType> expr, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<?> visit(
			final FuncLitExpr<ParamType, ResultType> expr, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final P param) {
		final Expr<ArrayType<IndexType, ElemType>> array = expr.getArray();
		final Expr<IndexType> index = expr.getIndex();

		@SuppressWarnings("unchecked")
		final Expr<ArrayType<IndexType, ElemType>> newArray = (Expr<ArrayType<IndexType, ElemType>>) array.accept(this,
				param);
		@SuppressWarnings("unchecked")
		final Expr<IndexType> newIndex = (Expr<IndexType>) index.accept(this, param);

		return expr.with(newArray, newIndex);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final P param) {

		final Expr<ArrayType<IndexType, ElemType>> array = expr.getArray();
		final Expr<IndexType> index = expr.getIndex();
		final Expr<ElemType> elem = expr.getElem();

		@SuppressWarnings("unchecked")
		final Expr<ArrayType<IndexType, ElemType>> newArray = (Expr<ArrayType<IndexType, ElemType>>) array.accept(this,
				param);
		@SuppressWarnings("unchecked")
		final Expr<IndexType> newIndex = (Expr<IndexType>) index.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<ElemType> newElem = (Expr<ElemType>) elem.accept(this, param);

		return expr.with(newArray, newIndex, newElem);
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(final ProcCallExpr<ReturnType> expr, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ExprType extends Type> Expr<ExprType> visit(final IteExpr<ExprType> expr, final P param) {
		final Expr<BoolType> cond = expr.getCond();
		final Expr<ExprType> then = expr.getThen();
		final Expr<ExprType> elze = expr.getElse();

		@SuppressWarnings("unchecked")
		final Expr<BoolType> newCond = (Expr<BoolType>) cond.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<ExprType> newThen = (Expr<ExprType>) then.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<ExprType> newElse = (Expr<ExprType>) elze.accept(this, param);

		return expr.withOps(newCond, newThen, newElse);
	}

	////

	@Override
	protected <ExprType extends Type> NullaryExpr<ExprType> visitNullary(final NullaryExpr<ExprType> expr,
			final P param) {
		return expr;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> UnaryExpr<OpType, ExprType> visitUnary(
			final UnaryExpr<OpType, ExprType> expr, final P param) {
		final Expr<OpType> op = expr.getOp();

		@SuppressWarnings("unchecked")
		final Expr<OpType> newOp = (Expr<OpType>) op.accept(this, param);

		return expr.withOp(newOp);
	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> BinaryExpr<LeftOpType, RightOpType, ExprType> visitBinary(
			final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final P param) {

		final Expr<LeftOpType> leftOp = expr.getLeftOp();
		final Expr<RightOpType> rightOp = expr.getRightOp();
		@SuppressWarnings("unchecked")
		final Expr<LeftOpType> newLeftOp = (Expr<LeftOpType>) leftOp.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<RightOpType> newRightOp = (Expr<RightOpType>) rightOp.accept(this, param);
		return expr.withOps(newLeftOp, newRightOp);
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> MultiaryExpr<OpsType, ExprType> visitMultiary(
			final MultiaryExpr<OpsType, ExprType> expr, final P param) {

		final Collection<? extends Expr<OpsType>> ops = expr.getOps();
		@SuppressWarnings("unchecked")
		final Collection<? extends Expr<OpsType>> newOps = Collections2.transform(ops,
				op -> (Expr<OpsType>) op.accept(this, param));

		return expr.withOps(newOps);
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<?> visitQuantified(final QuantifiedExpr expr,
			final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
