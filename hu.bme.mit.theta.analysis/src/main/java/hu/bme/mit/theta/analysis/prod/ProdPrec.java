package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.product.Product;

public abstract class ProdPrec implements Prec, Product, Iterable<Prec> {

	private static final int HASH_SEED = 2903;
	private volatile int hashCode = 0;

	private final List<Prec> precs;

	ProdPrec(final List<? extends Prec> prec) {
		this.precs = ImmutableList.copyOf(checkNotNull(prec));
	}

	////

	public static <P1 extends Prec, P2 extends Prec> Prod2Prec<P1, P2> of(final P1 prec1, final P2 prec2) {
		return new Prod2Prec<>(prec1, prec2);
	}

	public static <P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3Prec<P1, P2, P3> of(final P1 prec1,
			final P2 prec2, final P3 prec3) {
		return new Prod3Prec<>(prec1, prec2, prec3);
	}

	////

	@Override
	public final int arity() {
		return precs.size();
	}

	@Override
	public final Object elem(final int n) {
		checkElementIndex(n, arity());
		return precs.get(n);
	}

	@Override
	public final List<? extends Object> toList() {
		return precs;
	}

	@Override
	public final Iterator<Prec> iterator() {
		return precs.iterator();
	}

	////

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + precs.hashCode();
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
			return this.precs.equals(that.precs);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(precs).toString();
	}

}
