package hu.bme.mit.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkPositionIndex;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.Product2;

public final class CompositePrecision<P1 extends Precision, P2 extends Precision>
		implements Precision, Product2<P1, P2> {

	private static final int HASH_SEED = 5479;

	private volatile int hashCode = 0;

	private final P1 prec1;
	private final P2 prec2;

	private CompositePrecision(final P1 prec1, final P2 prec2) {
		this.prec1 = checkNotNull(prec1);
		this.prec2 = checkNotNull(prec2);
	}

	public static <P1 extends Precision, P2 extends Precision> CompositePrecision<P1, P2> create(final P1 prec1,
			final P2 prec2) {
		return new CompositePrecision<>(prec1, prec2);
	}

	@Override
	public P1 _1() {
		return prec1;
	}

	@Override
	public P2 _2() {
		return prec2;
	}

	@Override
	public int arity() {
		return 2;
	}

	@Override
	public Object elem(final int n) {
		checkPositionIndex(n, 2);
		return n == 0 ? _1() : _2();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + prec1.hashCode();
			result = 37 * result + prec2.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof CompositePrecision) {
			final CompositePrecision<?, ?> that = (CompositePrecision<?, ?>) obj;
			return this.prec1.equals(that.prec1) && this.prec2.equals(that.prec2);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("CompositePrecision").add(prec1).add(prec2).toString();
	}

}
