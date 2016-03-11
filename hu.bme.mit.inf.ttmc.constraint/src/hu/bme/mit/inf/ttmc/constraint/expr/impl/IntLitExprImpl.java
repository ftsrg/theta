package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNullaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class IntLitExprImpl extends AbstractNullaryExpr<IntType> implements IntLitExpr {

	private final long value;
	
	private volatile int hashCode = 0;
	
	public IntLitExprImpl(final long value) {
		this.value = value;
	}
	
	@Override
	public long getValue() {
		return value;
	}
	
	@Override
	public int compareTo(IntLitExpr that) {
		return Long.compare(this.getValue(), that.getValue());
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + (int)(value ^ (value >>> 32));
		}
		
		return hashCode;
	}
	
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final IntLitExprImpl that = (IntLitExprImpl) obj;
			return this.value == that.value;
		} else {
			return false;
		}
	}
	
	@Override
	public final String toString() {
		return Long.toString(getValue());
	}

	@Override
	protected int getHashSeed() {
		return 83;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
