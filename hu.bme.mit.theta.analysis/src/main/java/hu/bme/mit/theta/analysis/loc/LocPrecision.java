package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public abstract class LocPrecision<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements Precision {

	public static <P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocPrecision<P, L, E> create(
			final Function<? super L, ? extends P> mapping) {
		return new Generic<P, L, E>(mapping);
	}

	public static <P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocPrecision<P, L, E> constant(
			final P precision) {
		return new Constant<P, L, E>(precision);
	}

	public abstract P getPrecision(final L loc);

	/////

	public static final class Generic<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
			extends LocPrecision<P, L, E> {
		private final Function<? super L, ? extends P> mapping;

		private Generic(final Function<? super L, ? extends P> mapping) {
			this.mapping = checkNotNull(mapping);
		}

		@Override
		public P getPrecision(final L loc) {
			checkNotNull(loc);
			return mapping.apply(loc);
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(LocPrecision.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	public static final class Constant<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
			extends LocPrecision<P, L, E> {
		private final P precision;

		private Constant(final P precision) {
			this.precision = checkNotNull(precision);
		}

		@Override
		public P getPrecision(final L loc) {
			checkNotNull(loc);
			return precision;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(LocPrecision.class.getSimpleName()).add(getClass().getSimpleName())
					.add(precision).toString();
		}
	}

}
