package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocPrecision<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements Precision {

	private final Function<? super L, ? extends P> mapping;

	private LocPrecision(final Function<? super L, ? extends P> mapping) {
		this.mapping = checkNotNull(mapping);
	}

	public static <P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocPrecision<P, L, E> create(
			final Function<? super L, ? extends P> mapping) {
		return new LocPrecision<P, L, E>(mapping);
	}

	public static <P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocPrecision<P, L, E> constant(
			final P precision) {
		return create(l -> precision);
	}

	public P getPrecision(final L loc) {
		checkNotNull(loc);
		return mapping.apply(loc);
	}

}
