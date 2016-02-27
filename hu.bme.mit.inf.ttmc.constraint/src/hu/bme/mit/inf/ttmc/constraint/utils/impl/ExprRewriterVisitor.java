package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.Collection;

import com.google.common.collect.Collections2;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleProjExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class ExprRewriterVisitor<P> implements ExprVisitor<P, Expr<?>> {

	@Override
	public <ExprType extends ClosedUnderAdd> Expr<ExprType> visit(AddExpr<ExprType> expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(AndExpr expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public <DeclType extends Type> Expr<DeclType> visit(ConstRefExpr<DeclType> expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(EqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(ExistsExpr expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(FalseExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(ForallExpr expr, P param) {
		return visitUnary(expr, param);
	}

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
	public Expr<BoolType> visit(GeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(GtExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(IffExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(ImplyExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<IntType> visit(IntDivExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<IntType> visit(IntLitExpr expr, P param) {
		return visitNullary(expr, param);
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

	@Override
	public Expr<BoolType> visit(LeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(LtExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<IntType> visit(ModExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Expr<ExprType> visit(MulExpr<ExprType> expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Expr<ExprType> visit(NegExpr<ExprType> expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(NeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(NotExpr expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(OrExpr expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public <DeclType extends Type> Expr<?> visit(ParamRefExpr<DeclType> expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<RatType> visit(RatDivExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<RatType> visit(RatLitExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<IntType> visit(RemExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> Expr<ExprType> visit(SubExpr<ExprType> expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public Expr<BoolType> visit(TrueExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<?> visit(TupleLitExpr expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public Expr<?> visit(TupleProjExpr expr, P param) {
		return visitUnary(expr, param);
	}

	////

	private <ExprType extends Type> NullaryExpr<ExprType> visitNullary(NullaryExpr<ExprType> expr, P param) {
		return expr;
	}

	private <OpType extends Type, ExprType extends Type> UnaryExpr<OpType, ExprType> visitUnary(
			UnaryExpr<OpType, ExprType> expr, P param) {
		final Expr<? extends OpType> op = expr.getOp();

		@SuppressWarnings("unchecked")
		final Expr<? extends OpType> newOp = (Expr<? extends OpType>) op.accept(this, param);

		return expr.withOp(newOp);
	}

	private <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> BinaryExpr<LeftOpType, RightOpType, ExprType> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, P param) {

		final Expr<? extends LeftOpType> leftOp = expr.getLeftOp();
		final Expr<? extends RightOpType> rightOp = expr.getRightOp();
		@SuppressWarnings("unchecked")
		final Expr<? extends LeftOpType> newLeftOp = (Expr<? extends LeftOpType>) leftOp.accept(this, param);
		@SuppressWarnings("unchecked")
		final Expr<? extends RightOpType> newRightOp = (Expr<? extends RightOpType>) rightOp.accept(this, param);
		return expr.withOps(newLeftOp, newRightOp);
	}

	private <OpsType extends Type, ExprType extends Type> MultiaryExpr<OpsType, ExprType> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, P param) {

		final Collection<? extends Expr<? extends OpsType>> ops = expr.getOps();
		@SuppressWarnings("unchecked")
		final Collection<? extends Expr<? extends OpsType>> newOps = Collections2.transform(ops,
				op -> (Expr<? extends OpsType>) op.accept(this, param));

		return expr.withOps(newOps);
	}

}
