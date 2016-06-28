package hu.bme.mit.inf.ttmc.core.utils.impl;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

public abstract class DefaultValueExprVisitor<P, R> implements ExprVisitor<P, R> {

	protected abstract R defaultValue(P param);

	@Override
	public <DeclType extends Type> R visit(final ConstRefExpr<DeclType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <DeclType extends Type> R visit(final ParamRefExpr<DeclType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final FalseExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final TrueExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final NotExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final ImplyExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final IffExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final AndExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final OrExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final ExistsExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final ForallExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final EqExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final NeqExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final GeqExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final GtExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final LeqExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final LtExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final IntLitExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final IntDivExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final RemExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final ModExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final RatLitExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final RatDivExpr expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> R visit(final NegExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> R visit(final SubExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> R visit(final AddExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> R visit(final MulExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> R visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> R visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> R visit(final FuncLitExpr<ParamType, ResultType> expr,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> R visit(final FuncAppExpr<ParamType, ResultType> expr,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends Type> R visit(final IteExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

}
