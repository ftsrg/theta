package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class TrueExprImpl extends AbstractBoolLitExpr implements TrueExpr {

	private static final String OPERATOR = "True";

	@Override
	public final boolean getValue() {
		return true;
	}

	@Override
	public final String toString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 242181;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
