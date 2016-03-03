package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public class RatLitExprImpl extends AbstractNullaryExpr<RatType> implements RatLitExpr {
	
	private final long num;
	private final long denom;
	
	private volatile int hashCode = 0;

	public RatLitExprImpl(final long num, final long denom) {
		checkArgument(denom != 0);

		this.num= num;
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
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final RatLitExprImpl that = (RatLitExprImpl) obj;
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

}
