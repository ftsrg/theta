package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class NotExprImpl extends AbstractUnaryExpr<BoolType, BoolType> implements NotExpr {

	private static final String OPERAND = "Not";

	public NotExprImpl(final Expr<? extends BoolType> op) {
		super(op);
	}
	
	@Override
	public NotExpr withOp(Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new NotExprImpl(op);
		}
	}

	@Override
	protected final String getOperatorString() {
		return OPERAND;
	}

	@Override
	protected int getHashSeed() {
		return 127;
	}
}
