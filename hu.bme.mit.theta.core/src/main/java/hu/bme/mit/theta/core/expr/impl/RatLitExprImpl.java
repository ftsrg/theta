package hu.bme.mit.theta.core.expr.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Rat;

import com.google.common.math.LongMath;

import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class RatLitExprImpl extends AbstractNullaryExpr<RatType> implements RatLitExpr {

	private static final int HASH_SEED = 149;

	private final long num;
	private final long denom;

	private volatile int hashCode = 0;

	RatLitExprImpl(final long num, final long denom) {
		checkArgument(denom != 0);

		final long gcd = LongMath.gcd(Math.abs(num), Math.abs(denom));
		if (denom >= 0) {
			this.num = num / gcd;
			this.denom = denom / gcd;
		} else {
			this.num = -num / gcd;
			this.denom = -denom / gcd;
		}
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
	public int sign() {
		return (num < 0) ? -1 : (num == 0) ? 0 : 1;
	}

	@Override
	public long floor() {
		if (num >= 0 || num % denom == 0) {
			return num / denom;
		} else {
			return num / denom - 1;
		}
	}

	@Override
	public long ceil() {
		if (num <= 0 || num % denom == 0) {
			return num / denom;
		} else {
			return num / denom + 1;
		}
	}

	@Override
	public RatLitExpr add(final RatLitExpr that) {
		return Rat(this.getNum() * that.getDenom() + this.getDenom() * that.getNum(),
				this.getDenom() * that.getDenom());
	}

	@Override
	public RatLitExpr sub(final RatLitExpr that) {
		return Rat(this.getNum() * that.getDenom() - this.getDenom() * that.getNum(),
				this.getDenom() * that.getDenom());
	}

	@Override
	public RatLitExpr mul(final RatLitExpr that) {
		return Rat(this.getNum() * that.getNum(), this.getDenom() * that.getDenom());
	}

	@Override
	public RatLitExpr div(final RatLitExpr that) {
		return Rat(this.getNum() * that.getDenom(), this.getDenom() * that.getNum());
	}

	@Override
	public RatLitExpr abs() {
		return Rat(Math.abs(num), denom);
	}

	@Override
	public RatLitExpr frac() {
		return sub(Rat(floor(), 1));
	}

	@Override
	public RatType getType() {
		return Types.Rat();
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
			result = 31 * result + (int) (num ^ (num >>> 32));
			result = 31 * result + (int) (denom ^ (denom >>> 32));
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatLitExpr) {
			final RatLitExpr that = (RatLitExpr) obj;
			return (this.getNum() == that.getNum() && this.getDenom() == that.getDenom());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getNum());
		sb.append("%");
		sb.append(getDenom());
		return sb.toString();
	}

	@Override
	public int compareTo(final RatLitExpr that) {
		return Long.compare(LongMath.checkedMultiply(this.getNum(), that.getDenom()),
				LongMath.checkedMultiply(that.getNum(), this.getDenom()));
	}

}
