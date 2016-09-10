package hu.bme.mit.theta.core.expr.impl;

import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class IntLitExprImpl extends AbstractNullaryExpr<IntType> implements IntLitExpr {

	private static final int HASH_SEED = 4111;

	private final long value;

	private volatile int hashCode = 0;

	IntLitExprImpl(final long value) {
		this.value = value;
	}

	@Override
	public long getValue() {
		return value;
	}

	@Override
	public IntType getType() {
		return Types.Int();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + (int) (value ^ (value >>> 32));
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntLitExpr) {
			final IntLitExpr that = (IntLitExpr) obj;
			return this.getValue() == that.getValue();
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Long.toString(getValue());
	}

	@Override
	public int compareTo(final IntLitExpr that) {
		return Long.compare(this.getValue(), that.getValue());
	}

}
