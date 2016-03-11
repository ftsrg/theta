package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractUnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class NegExprImpl<ExprType extends ClosedUnderNeg> extends AbstractUnaryExpr<ExprType, ExprType> implements NegExpr<ExprType> {

	private static final String OPERATOR = "Neg";
		
	public NegExprImpl(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public NegExpr<ExprType> withOp(Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new NegExprImpl<>(op);
		}
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 97;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
