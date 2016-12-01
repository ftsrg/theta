package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.AndExpr;
import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.ExistsExpr;
import hu.bme.mit.theta.core.expr.FalseExpr;
import hu.bme.mit.theta.core.expr.ForallExpr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IffExpr;
import hu.bme.mit.theta.core.expr.ImplyExpr;
import hu.bme.mit.theta.core.expr.IntDivExpr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.ModExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.expr.OrExpr;
import hu.bme.mit.theta.core.expr.ParamRefExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.expr.RemExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.TrueExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.utils.ExprVisitor;

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
	public <DeclType extends Type> R visit(final VarRefExpr<DeclType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ReturnType extends Type> R visit(final ProcRefExpr<ReturnType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends Type> R visit(final PrimedExpr<ExprType> expr, final P param) {
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
	public <ReturnType extends Type> R visit(final ProcCallExpr<ReturnType> expr, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ExprType extends Type> R visit(final IteExpr<ExprType> expr, final P param) {
		return defaultValue(param);
	}

}
