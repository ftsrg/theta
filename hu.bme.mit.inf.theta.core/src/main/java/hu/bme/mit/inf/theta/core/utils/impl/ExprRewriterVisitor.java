package hu.bme.mit.inf.theta.core.utils.impl;

import java.util.Collection;

import com.google.common.collect.Collections2;

import hu.bme.mit.inf.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.theta.core.expr.BinaryExpr;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.FuncAppExpr;
import hu.bme.mit.inf.theta.core.expr.FuncLitExpr;
import hu.bme.mit.inf.theta.core.expr.IteExpr;
import hu.bme.mit.inf.theta.core.expr.MultiaryExpr;
import hu.bme.mit.inf.theta.core.expr.NullaryExpr;
import hu.bme.mit.inf.theta.core.expr.UnaryExpr;
import hu.bme.mit.inf.theta.core.type.ArrayType;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public class ExprRewriterVisitor<P> extends ArityBasedExprVisitor<P, Expr<?>> {

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<ResultType> visit(
			FuncAppExpr<ParamType, ResultType> expr, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<?> visit(FuncLitExpr<ParamType, ResultType> expr,
			P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(ArrayReadExpr<IndexType, ElemType> expr,
			P param) {
		final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array = expr.getArray();
		final Expr<? extends IndexType> index = expr.getIndex();

		@SuppressWarnings("unchecked")
		final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> newArray = (Expr<? extends ArrayType<? super IndexType, ? extends ElemType>>) array
				.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends IndexType> newIndex = (Expr<? extends IndexType>) index.accept(this, param);

		return expr.with(newArray, newIndex);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(ArrayWriteExpr<IndexType, ElemType> expr,
			P param) {
		
		final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array = expr.getArray();
		final Expr<? extends IndexType> index = expr.getIndex();
		final Expr<? extends ElemType> elem = expr.getElem();

		@SuppressWarnings("unchecked")
		final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> newArray = (Expr<? extends ArrayType<? super IndexType, ? extends ElemType>>) array
				.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends IndexType> newIndex = (Expr<? extends IndexType>) index.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends ElemType> newElem = (Expr<? extends ElemType>) elem.accept(this, param);

		return expr.with(newArray, newIndex, newElem);
	}

	@Override
	public <ExprType extends Type> Expr<ExprType> visit(IteExpr<ExprType> expr, P param) {
		final Expr<? extends BoolType> cond = expr.getCond();
		final Expr<? extends ExprType> then = expr.getThen();
		final Expr<? extends ExprType> elze = expr.getElse();

		@SuppressWarnings("unchecked")
		final Expr<? extends BoolType> newCond = (Expr<? extends BoolType>) cond.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> newThen = (Expr<? extends ExprType>) then.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> newElse = (Expr<? extends ExprType>) elze.accept(this, param);

		return expr.withOps(newCond, newThen, newElse);
	}

	////

	@Override
	protected <ExprType extends Type> NullaryExpr<ExprType> visitNullary(NullaryExpr<ExprType> expr, P param) {
		return expr;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> UnaryExpr<OpType, ExprType> visitUnary(
			UnaryExpr<OpType, ExprType> expr, P param) {
		final Expr<? extends OpType> op = expr.getOp();

		@SuppressWarnings("unchecked")
		final Expr<? extends OpType> newOp = (Expr<? extends OpType>) op.accept(this, param);

		return expr.withOp(newOp);
	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> BinaryExpr<LeftOpType, RightOpType, ExprType> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, P param) {

		final Expr<? extends LeftOpType> leftOp = expr.getLeftOp();
		final Expr<? extends RightOpType> rightOp = expr.getRightOp();
		@SuppressWarnings("unchecked")
		final Expr<? extends LeftOpType> newLeftOp = (Expr<? extends LeftOpType>) leftOp.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends RightOpType> newRightOp = (Expr<? extends RightOpType>) rightOp.accept(this, param);
		return expr.withOps(newLeftOp, newRightOp);
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> MultiaryExpr<OpsType, ExprType> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, P param) {

		final Collection<? extends Expr<? extends OpsType>> ops = expr.getOps();
		@SuppressWarnings("unchecked")
		final Collection<? extends Expr<? extends OpsType>> newOps = Collections2.transform(ops,
				op -> (Expr<? extends OpsType>) op.accept(this, param));

		return expr.withOps(newOps);
	}

}
