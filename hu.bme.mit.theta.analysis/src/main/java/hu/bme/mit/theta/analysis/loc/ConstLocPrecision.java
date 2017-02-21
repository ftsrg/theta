package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

/**
 * Represents an immutable constant precision.
 */
public final class ConstLocPrecision<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LocPrecision<P, L, E> {

	private final P precision;

	private ConstLocPrecision(final P precision) {
		this.precision = checkNotNull(precision);
	}

	public static <P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> ConstLocPrecision<P, L, E> create(
			final P precision) {
		return new ConstLocPrecision<>(precision);
	}

	public ConstLocPrecision<P, L, E> refine(final P refinedPrecision) {
		if (this.precision == refinedPrecision) {
			return this;
		} else {
			return create(refinedPrecision);
		}
	}

	@Override
	public P getPrecision(final L loc) {
		checkNotNull(loc);
		return precision;
	}

	public P getPrecision() {
		return precision;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(precision).toString();
	}

}
