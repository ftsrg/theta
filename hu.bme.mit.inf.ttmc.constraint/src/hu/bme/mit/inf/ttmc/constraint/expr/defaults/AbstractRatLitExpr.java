package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractRatLitExpr extends AbstractNullaryExpr<RatType> implements RatLitExpr {

	private final long num;
	private final long denom;

	private volatile int hashCode = 0;

	public AbstractRatLitExpr(final long num, final long denom) {
		checkArgument(denom != 0);

		this.num = num;
		this.denom = denom;
	}

	@Override
	public long getNum() {
		return num;
	}

	@Override
	public long getDenom() {
		return denom;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + (int) (num ^ (num >>> 32));
			hashCode = 31 * hashCode + (int) (denom ^ (denom >>> 32));
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
			final AbstractRatLitExpr that = (AbstractRatLitExpr) obj;
			return (this.num == that.num && this.denom == that.denom);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getNum());
		sb.append("%");
		sb.append(getDenom());
		return sb.toString();
	}

	@Override
	protected int getHashSeed() {
		return 149;
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}
}
