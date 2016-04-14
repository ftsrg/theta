package hu.bme.mit.inf.ttmc.core.utils.impl;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableSet;

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
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class ExprITERemoverVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(final NullaryExpr<ExprType> expr, final Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(final UnaryExpr<OpType, ExprType> expr, final Void param) {
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
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(final MultiaryExpr<OpsType, ExprType> expr, final Void param) {
		final List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (final Expr<? extends OpsType> op : expr.getOps())
			ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(final ArrayReadExpr<IndexType, ElemType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(final ArrayWriteExpr<IndexType, ElemType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(final FuncLitExpr<ParamType, ResultType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(final FuncAppExpr<ParamType, ResultType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@SuppressWarnings("unchecked")
	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(final IteExpr<ExprType> expr, final Void param) {
		// Apply ite(C,T,E) <=> (!C or T) and (C or E) transformation
		final Expr<? extends BoolType> cond = (Expr<? extends BoolType>) expr.getCond().accept(this, param);
		final Expr<? extends Type> then = expr.getThen().accept(this, param);
		final Expr<? extends Type> elze = expr.getElse().accept(this, param);
		return Exprs.And(ImmutableSet.of(Exprs.Or(ImmutableSet.of(Exprs.Not(cond), (Expr<? extends BoolType>) then)),
				Exprs.Or(ImmutableSet.of(cond, (Expr<? extends BoolType>) elze))));
	}

}
