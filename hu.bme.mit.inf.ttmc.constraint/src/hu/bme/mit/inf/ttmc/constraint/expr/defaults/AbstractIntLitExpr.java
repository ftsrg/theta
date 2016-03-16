package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractIntLitExpr extends AbstractNullaryExpr<IntType> implements IntLitExpr {

	private static final int HASH_SEED = 4111;

	private final long value;

	private volatile int hashCode = 0;

	public AbstractIntLitExpr(final long value) {
		this.value = value;
	}

	@Override
	public final long getValue() {
		return value;
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + (int) (value ^ (value >>> 32));
		}

		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
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
	public final String toString() {
		return Long.toString(getValue());
	}

	@Override
	public final int compareTo(final IntLitExpr that) {
		return Long.compare(this.getValue(), that.getValue());
	}

}
