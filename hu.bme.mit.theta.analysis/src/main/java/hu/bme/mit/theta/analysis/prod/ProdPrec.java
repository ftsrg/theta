package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.Product;

public abstract class ProdPrec implements Prec, Product, Iterable<Prec> {

	private static final int HASH_SEED = 2903;
	private volatile int hashCode = 0;

	private final List<Prec> precisions;

	ProdPrec(final List<? extends Prec> precisions) {
		this.precisions = ImmutableList.copyOf(checkNotNull(precisions));
	}

	////

	public static <P1 extends Prec, P2 extends Prec> Prod2Prec<P1, P2> of(final P1 precision1,
			final P2 precision2) {
		return new Prod2Prec<>(precision1, precision2);
	}

	public static <P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3Prec<P1, P2, P3> of(
			final P1 precision1, final P2 precision2, final P3 precision3) {
		return new Prod3Prec<>(precision1, precision2, precision3);
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
	public final Iterator<Prec> iterator() {
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
		} else if (obj instanceof ProdPrec) {
			final ProdPrec that = (ProdPrec) obj;
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
