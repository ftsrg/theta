package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.expr.AbstractExprs.Ite;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.proctype.ProcCallExpr;

public class ItePusherVisitor extends ArityBasedExprVisitor<Void, Expr<?>> {

	@Override
	protected <ExprType extends Type> Expr<?> visitNullary(final NullaryExpr<ExprType> expr, final Void param) {
		return expr;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<?> visitUnary(final UnaryExpr<OpType, ExprType> expr,
			final Void param) {
		// Nothing to do if the operand is not an ITE or it is of bool type
		if (!(expr.getOp() instanceof IteExpr) || expr.getOp().getType() instanceof BoolType) {
			return expr;
		} else {
			// Push expression below ITE, e.g., -ite(C,T,E) => ite(C,-T,-E)
			final IteExpr<OpType> op = (IteExpr<OpType>) expr.getOp();
			return Ite(op.getCond(), expr.withOp(op.getThen()).accept(this, param),
					expr.withOp(op.getElse()).accept(this, param));
		}

	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<?> visitBinary(
			final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Void param) {
		// Nothing to do if the none of the operands are ITE
		if (!(expr.getLeftOp() instanceof IteExpr || expr.getRightOp() instanceof IteExpr)) {
			return expr;
		} else if (expr.getLeftOp() instanceof IteExpr && !(expr.getLeftOp().getType() instanceof BoolType)) {
			// Push expression below ITE, e.g., ite(C,T,E) = X => ite(C,T=X,E=X)
			final IteExpr<LeftOpType> op = (IteExpr<LeftOpType>) expr.getLeftOp();
			return Ite(op.getCond(), expr.withLeftOp(op.getThen()).accept(this, param),
					expr.withLeftOp(op.getElse()).accept(this, param));
		} else if (expr.getRightOp() instanceof IteExpr && !(expr.getRightOp().getType() instanceof BoolType)) {
			// Push expression below ITE, e.g., X = ite(C,T,E) => ite(C,x=T,X=E)
			final IteExpr<RightOpType> op = (IteExpr<RightOpType>) expr.getRightOp();
			return Ite(op.getCond(), expr.withRightOp(op.getThen()).accept(this, param),
					expr.withRightOp(op.getElse()).accept(this, param));
		} else {
			return expr;
		}
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<?> visitMultiary(
			final MultiaryExpr<OpsType, ExprType> expr, final Void param) {
		// Get the first operand which is an ITE
		final Optional<? extends Expr<OpsType>> firstIte = expr.getOps().stream().filter(op -> op instanceof IteExpr)
				.findFirst();
		// Nothing to do if the none of the operands are ITE or it is of bool
		// type
		if (!firstIte.isPresent() || expr.getOps().size() == 0
				|| expr.getOps().iterator().next().getType() instanceof BoolType) {
			return expr;
		} else {
			// Push expression below ITE, e.g., X + ite(C,T,E) + Y =>
			// ite(C,X+T+Y,X+E+Y)
			final List<Expr<OpsType>> thenOps = new ArrayList<>(expr.getOps().size());
			final List<Expr<OpsType>> elseOps = new ArrayList<>(expr.getOps().size());
			final IteExpr<OpsType> ite = (IteExpr<OpsType>) firstIte.get();

			for (final Expr<OpsType> op : expr.getOps()) {
				if (op == ite) {
					thenOps.add(ite.getThen());
					elseOps.add(ite.getElse());
				} else {
					thenOps.add(op);
					elseOps.add(op);
				}
			}

			return Ite(ite.getCond(), expr.withOps(thenOps).accept(this, param),
					expr.withOps(elseOps).accept(this, param));
		}
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<?> visitQuantified(final QuantifiedExpr expr,
			final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<?> visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<?> visit(
			final FuncLitExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<?> visit(
			final FuncAppExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(final ProcCallExpr<ReturnType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ExprType extends Type> Expr<?> visit(final IteExpr<ExprType> expr, final Void param) {
		return expr;
	}

}
