package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

/**
 * Represents an immutable constant precision.
 */
public final class ConstLocPrec<P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LocPrec<P, L, E> {

	private final P precision;

	private ConstLocPrec(final P precision) {
		this.precision = checkNotNull(precision);
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> ConstLocPrec<P, L, E> create(
			final P precision) {
		return new ConstLocPrec<>(precision);
	}

	public ConstLocPrec<P, L, E> refine(final P refinedPrecision) {
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
