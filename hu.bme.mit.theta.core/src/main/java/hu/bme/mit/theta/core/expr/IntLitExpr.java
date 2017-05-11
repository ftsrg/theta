package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntLitExpr extends NullaryExpr<IntType> implements LitExpr<IntType>, Comparable<IntLitExpr> {

	private static final int HASH_SEED = 4111;
	private volatile int hashCode = 0;

	private final int value;
	private volatile RatLitExpr ratLitExpr = null;

	IntLitExpr(final int value) {
		this.value = value;
	}

	public int getValue() {
		return value;
	}

	public RatLitExpr toRatLit() {
		RatLitExpr result = ratLitExpr;
		if (result == null) {
			result = Exprs.Rat(value, 1);
			ratLitExpr = result;
		}
		return result;
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
			result = 31 * result + value;
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
