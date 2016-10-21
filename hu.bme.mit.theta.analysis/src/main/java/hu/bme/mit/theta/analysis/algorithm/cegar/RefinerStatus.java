package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public abstract class RefinerStatus<S extends State, A extends Action, P extends Precision> {

	private RefinerStatus() {
	}

	public static <S extends State, A extends Action, P extends Precision> Spurious<S, A, P> spurious(
			final ARG<S, A> prunedArg, final P refinedPrecision) {
		return new Spurious<>(prunedArg, refinedPrecision);
	}

	public static <S extends State, A extends Action, P extends Precision> Concretizable<S, A, P> concretizable(
			final Trace<S, A> cex) {
		return new Concretizable<>(cex);
	}

	public abstract boolean isSpurious();

	public abstract boolean isConcretizable();

	public abstract Spurious<S, A, P> asSpurious();

	public abstract Concretizable<S, A, P> asConcretizable();

	////

	public static final class Spurious<S extends State, A extends Action, P extends Precision>
			extends RefinerStatus<S, A, P> {
		private final ARG<S, A> prunedArg;
		private final P refinedPrecision;

		private Spurious(final ARG<S, A> prunedArg, final P refinedPrecision) {
			this.prunedArg = checkNotNull(prunedArg);
			this.refinedPrecision = checkNotNull(refinedPrecision);
		}

		public ARG<S, A> getPrunedArg() {
			return prunedArg;
		}

		public P getRefinedPrecision() {
			return refinedPrecision;
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
		public Spurious<S, A, P> asSpurious() {
			return this;
		}

		@Override
		public Concretizable<S, A, P> asConcretizable() {
			throw new ClassCastException("Trying to cast a Spurious to Concretizable");
		}
	}

	public static final class Concretizable<S extends State, A extends Action, P extends Precision>
			extends RefinerStatus<S, A, P> {
		private final Trace<S, A> cex;

		private Concretizable(final Trace<S, A> cex) {
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
		public boolean isConcretizable() {
			return true;
		}

		@Override
		public Spurious<S, A, P> asSpurious() {
			throw new ClassCastException("Trying to cast a Concretizable to Spurious");
		}

		@Override
		public Concretizable<S, A, P> asConcretizable() {
			return this;
		}
	}
}
