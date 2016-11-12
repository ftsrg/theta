package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.common.ObjectUtils;

public abstract class CexStatus<R extends Refutation> {

	private CexStatus() {
	}

	public static <R extends Refutation> Spurious<R> spurious(final R refutation) {
		return new Spurious<>(refutation);
	}

	public static <R extends Refutation> Concretizable<R> concretizable() {
		return new Concretizable<>();
	}

	public abstract boolean isSpurious();

	public abstract boolean isConcretizable();

	public abstract Spurious<R> asSpurious();

	public abstract Concretizable<R> asConcretizable();

	public final static class Spurious<R extends Refutation> extends CexStatus<R> {
		private final R refutation;

		private Spurious(final R refutation) {
			this.refutation = checkNotNull(refutation);
		}

		public R getRefutation() {
			return refutation;
		}

		@Override
		public boolean isSpurious() {
			return true;
		}

		@Override
		public boolean isConcretizable() {
			return false;
		}

		@Override
		public Spurious<R> asSpurious() {
			return this;
		}

		@Override
		public Concretizable<R> asConcretizable() {
			throw new ClassCastException(
					"Cannot cast " + Spurious.class.getSimpleName() + " to " + Concretizable.class.getSimpleName());
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(CexStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}

	public final static class Concretizable<R extends Refutation> extends CexStatus<R> {

		@Override
		public boolean isSpurious() {
			return false;
		}

		@Override
		public boolean isConcretizable() {
			return true;
		}

		@Override
		public Spurious<R> asSpurious() {
			throw new ClassCastException(
					"Cannot cast " + Concretizable.class.getSimpleName() + " to " + Spurious.class.getSimpleName());
		}

		@Override
		public Concretizable<R> asConcretizable() {
			return this;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(CexStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}
}
