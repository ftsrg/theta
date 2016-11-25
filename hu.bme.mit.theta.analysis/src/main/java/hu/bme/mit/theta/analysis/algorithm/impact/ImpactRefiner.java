package hu.bme.mit.theta.analysis.algorithm.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface ImpactRefiner<S extends State, A extends Action> {

	RefinementResult<S, A> refine(final Trace<S, A> cex);

	static abstract class RefinementResult<S extends State, A extends Action> {

		private RefinementResult() {
		}

		public static <S extends State, A extends Action> Succesful<S, A> succesful(final Trace<S, A> trace) {
			return new Succesful<>(trace);
		}

		public static <S extends State, A extends Action> Unsuccesful<S, A> unsuccesful() {
			return new Unsuccesful<>();
		}

		public abstract boolean isSuccesful();

		public abstract boolean isUnsuccesful();

		public abstract Succesful<S, A> asSuccesful();

		public abstract Unsuccesful<S, A> asUnsuccesful();
	}

	static final class Succesful<S extends State, A extends Action> extends RefinementResult<S, A> {
		private final Trace<S, A> trace;

		private Succesful(final Trace<S, A> trace) {
			this.trace = checkNotNull(trace);
		}

		public Trace<S, A> getTrace() {
			return trace;
		}

		@Override
		public boolean isSuccesful() {
			return true;
		}

		@Override
		public boolean isUnsuccesful() {
			return false;
		}

		@Override
		public Succesful<S, A> asSuccesful() {
			return this;
		}

		@Override
		public Unsuccesful<S, A> asUnsuccesful() {
			throw new ClassCastException();
		}
	}

	static final class Unsuccesful<S extends State, A extends Action> extends RefinementResult<S, A> {

		private Unsuccesful() {
		}

		@Override
		public boolean isSuccesful() {
			return false;
		}

		@Override
		public boolean isUnsuccesful() {
			return true;
		}

		@Override
		public Succesful<S, A> asSuccesful() {
			throw new ClassCastException();
		}

		@Override
		public Unsuccesful<S, A> asUnsuccesful() {
			return this;
		}
	}

}
