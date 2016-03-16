package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractUnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.PrimedExprVisitor;

public final class PrimedExprImpl<ExprType extends Type> extends AbstractUnaryExpr<ExprType, ExprType>
		implements PrimedExpr<ExprType> {

	private static final int HASH_SEED = 4561;

	private static final String OPERATOR_LABEL = "Prime";

	public PrimedExprImpl(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public final UnaryExpr<ExprType, ExprType> withOp(final Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new PrimedExprImpl<>(op);
		}
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof PrimedExprVisitor<?, ?>) {
			final PrimedExprVisitor<? super P, ? extends R> sVisitor = (PrimedExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
