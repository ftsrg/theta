package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.common.ObjectUtils;

public abstract class RefinerStatus<S extends State, A extends Action, P extends Precision> {
	private final AbstractionState<S, A, P> abstractionState;

	private RefinerStatus(final AbstractionState<S, A, P> abstractionState) {
		this.abstractionState = checkNotNull(abstractionState);
	}

	public ARG<S, A> getArg() {
		return abstractionState.getArg();
	}

	public AbstractionState<S, A, P> getAbstractionState() {
		return abstractionState;
	}

	public static <S extends State, A extends Action, P extends Precision> Spurious<S, A, P> spurious(
			final AbstractionState<S, A, P> abstractionState, final P refinedPrecision) {
		return new Spurious<>(abstractionState, refinedPrecision);
	}

	public static <S extends State, A extends Action, P extends Precision> Concretizable<S, A, P> concretizable(
			final AbstractionState<S, A, P> abstractionState, final Trace<S, A> cex) {
		return new Concretizable<>(abstractionState, cex);
	}

	public abstract boolean isSpurious();

	public abstract boolean isConcretizable();

	public abstract Spurious<S, A, P> asSpurious();

	public abstract Concretizable<S, A, P> asConcretizable();

	////

	public static final class Spurious<S extends State, A extends Action, P extends Precision>
			extends RefinerStatus<S, A, P> {
		private final P refinedPrecision;

		private Spurious(final AbstractionState<S, A, P> abstractionState, final P refinedPrecision) {
			super(abstractionState);
			this.refinedPrecision = checkNotNull(refinedPrecision);
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
			throw new ClassCastException(
					"Cannot cast " + Spurious.class.getSimpleName() + " to " + Concretizable.class.getSimpleName());
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(RefinerStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	public static final class Concretizable<S extends State, A extends Action, P extends Precision>
			extends RefinerStatus<S, A, P> {
		private final Trace<S, A> cex;

		private Concretizable(final AbstractionState<S, A, P> abstractionState, final Trace<S, A> cex) {
			super(abstractionState);
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
			throw new ClassCastException(
					"Cannot cast " + Concretizable.class.getSimpleName() + " to " + Spurious.class.getSimpleName());
		}

		@Override
		public Concretizable<S, A, P> asConcretizable() {
			return this;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(RefinerStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}
}
