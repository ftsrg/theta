package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractBoolLitExpr;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class FalseExprImpl extends AbstractBoolLitExpr implements FalseExpr {

	private static final String OPERATOR = "False";

	@Override
	public final boolean getValue() {
		return false;
	}

	@Override
	public int hashCode() {
		return getHashSeed();
	}

	@Override
	public final String toString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 712514;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
