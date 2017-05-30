package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.QuantifiedExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.inttype.RemExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public abstract class ArityBasedExprVisitor<P, R> implements ExprVisitor<P, R> {

	protected abstract <ExprType extends Type> R visitNullary(NullaryExpr<ExprType> expr, P param);

	protected abstract <OpType extends Type, ExprType extends Type> R visitUnary(UnaryExpr<OpType, ExprType> expr,
			P param);

	protected abstract <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> R visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, P param);

	protected abstract <OpsType extends Type, ExprType extends Type> R visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, P param);

	protected abstract <OpsType extends Type, ExprType extends Type> R visitQuantified(QuantifiedExpr expr, P param);

	@Override
	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayReadExpr<IndexType, ElemType> expr,
			P param);

	@Override
	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayWriteExpr<IndexType, ElemType> expr,
			P param);

	@Override
	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncLitExpr<ParamType, ResultType> expr,
			P param);

	@Override
	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncAppExpr<ParamType, ResultType> expr,
			P param);

	@Override
	public abstract <ReturnType extends Type> R visit(final ProcCallExpr<ReturnType> expr, final P param);

	@Override
	public abstract <ExprType extends Type> R visit(IteExpr<ExprType> expr, P param);

	/////

	@Override
	public <DeclType extends Type> R visit(final RefExpr<DeclType> expr, final P param) {
		return visitNullary(expr, param);
	}

	@Override
	public <ExprType extends Type> R visit(final PrimedExpr<ExprType> expr, final P param) {
		return visitUnary(expr, param);
	}

	@Override
	public R visit(final FalseExpr expr, final P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(final TrueExpr expr, final P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(final NotExpr expr, final P param) {
		return visitUnary(expr, param);
	}

	@Override
	public R visit(final ImplyExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final IffExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final AndExpr expr, final P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public R visit(final OrExpr expr, final P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public R visit(final ExistsExpr expr, final P param) {
		return visitQuantified(expr, param);
	}

	@Override
	public R visit(final ForallExpr expr, final P param) {
		return visitQuantified(expr, param);
	}

	@Override
	public R visit(final EqExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final NeqExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final GeqExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final GtExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final LeqExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final LtExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final IntLitExpr expr, final P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(final IntDivExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final RemExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final ModExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(final RatLitExpr expr, final P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(final RatDivExpr expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> R visit(final NegExpr<ExprType> expr, final P param) {
		return visitUnary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> R visit(final SubExpr<ExprType> expr, final P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> R visit(final AddExpr<ExprType> expr, final P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> R visit(final MulExpr<ExprType> expr, final P param) {
		return visitMultiary(expr, param);
	}

}
