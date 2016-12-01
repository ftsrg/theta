package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.Product;

public abstract class ProdPrecision implements Precision, Product, Iterable<Precision> {

	private static final int HASH_SEED = 2903;
	private volatile int hashCode = 0;

	private final List<Precision> precisions;

	ProdPrecision(final List<? extends Precision> precisions) {
		this.precisions = ImmutableList.copyOf(checkNotNull(precisions));
	}

	////

	public static <P1 extends Precision, P2 extends Precision> Prod2Precision<P1, P2> of(final P1 precision1,
			final P2 precision2) {
		return new Prod2Precision<>(precision1, precision2);
	}

	public static <P1 extends Precision, P2 extends Precision, P3 extends Precision> Prod3Precision<P1, P2, P3> of(
			final P1 precision1, final P2 precision2, final P3 precision3) {
		return new Prod3Precision<>(precision1, precision2, precision3);
	}

	////

	@Override
	public final int arity() {
		return precisions.size();
	}

	@Override
	public final Object elem(final int n) {
		checkElementIndex(n, arity());
		return precisions.get(n);
	}

	@Override
	public final List<? extends Object> toList() {
		return precisions;
	}

	@Override
	public final Iterator<Precision> iterator() {
		return precisions.iterator();
	}

	////

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + precisions.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProdPrecision) {
			final ProdPrecision that = (ProdPrecision) obj;
			return this.precisions.equals(that.precisions);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder("ProdPrecision").addAll(precisions).toString();
	}

}
