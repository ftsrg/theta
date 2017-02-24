package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.ObjectUtils;

public abstract class RefinerResult<S extends State, A extends Action, P extends Prec> {

	private RefinerResult() {
	}

	public static <S extends State, A extends Action, P extends Prec> Spurious<S, A, P> spurious(
			final P refinedPrec) {
		return new Spurious<>(refinedPrec);
	}

	public static <S extends State, A extends Action, P extends Prec> Unsafe<S, A, P> unsafe(
			final Trace<S, A> cex) {
		return new Unsafe<>(cex);
	}

	public abstract boolean isSpurious();

	public abstract boolean isUnsafe();

	public abstract Spurious<S, A, P> asSpurious();

	public abstract Unsafe<S, A, P> asUnsafe();

	////

	public static final class Spurious<S extends State, A extends Action, P extends Prec>
			extends RefinerResult<S, A, P> {
		private final P refinedPrec;

		private Spurious(final P refinedPrec) {
			this.refinedPrec = checkNotNull(refinedPrec);
		}

		public P getRefinedPrec() {
			return refinedPrec;
		}

		@Override
		public boolean isSpurious() {
			return true;
		}

		@Override
		public boolean isUnsafe() {
			return false;
		}

		@Override
		public Spurious<S, A, P> asSpurious() {
			return this;
		}

		@Override
		public Unsafe<S, A, P> asUnsafe() {
			throw new ClassCastException(
					"Cannot cast " + Spurious.class.getSimpleName() + " to " + Unsafe.class.getSimpleName());
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(RefinerResult.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	public static final class Unsafe<S extends State, A extends Action, P extends Prec>
			extends RefinerResult<S, A, P> {
		private final Trace<S, A> cex;

		private Unsafe(final Trace<S, A> cex) {
			this.cex = checkNotNull(cex);
		}

		public Trace<S, A> getCex() {
			return cex;
		}

		@Override
		public boolean isSpurious() {
			return false;
		}

		@Override
		public boolean isUnsafe() {
			return true;
		}

		@Override
		public Spurious<S, A, P> asSpurious() {
			throw new ClassCastException(
					"Cannot cast " + Unsafe.class.getSimpleName() + " to " + Spurious.class.getSimpleName());
		}

		@Override
		public Unsafe<S, A, P> asUnsafe() {
			return this;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(RefinerResult.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}
}
