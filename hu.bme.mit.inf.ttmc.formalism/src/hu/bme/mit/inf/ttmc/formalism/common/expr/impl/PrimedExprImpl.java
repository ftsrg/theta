package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.AbstractUnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.PrimedExprVisitor;

public final class PrimedExprImpl<ExprType extends Type> extends AbstractUnaryExpr<ExprType, ExprType> implements PrimedExpr<ExprType> {

	private static final String OPERAND = "\'";
	
	
	public PrimedExprImpl(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public UnaryExpr<ExprType, ExprType> withOp(Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new PrimedExprImpl<>(op);
		}
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(getOp().toString());
		sb.append(")'");
		return sb.toString();
	}

	@Override
	protected String getOperatorString() {
		return OPERAND;
	}

	@Override
	protected int getHashSeed() {
		return 317;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		if (visitor instanceof PrimedExprVisitor<?, ?>) {
			final PrimedExprVisitor<? super P, ? extends R> sVisitor = (PrimedExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
