package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.ObjectUtils;

public abstract class SafetyStatus<S extends State, A extends Action> {
	private final ARG<S, A> arg;

	private SafetyStatus(final ARG<S, A> arg) {
		this.arg = checkNotNull(arg);
	}

	public ARG<S, A> getArg() {
		return arg;
	}

	public static <S extends State, A extends Action> Safe<S, A> safe(final ARG<S, A> arg) {
		return new Safe<>(arg);
	}

	public static <S extends State, A extends Action> Unsafe<S, A> unsafe(final Trace<S, A> cex, final ARG<S, A> arg) {
		return new Unsafe<>(cex, arg);
	}

	public abstract boolean isSafe();

	public abstract boolean isUnsafe();

	public abstract Safe<S, A> asSafe();

	public abstract Unsafe<S, A> asUnsafe();

	////

	public static final class Safe<S extends State, A extends Action> extends SafetyStatus<S, A> {
		private Safe(final ARG<S, A> arg) {
			super(arg);
			checkArgument(arg.isInitialized());
			checkArgument(arg.isComplete());
			// checkArgument(arg.isSafe());
		}

		@Override
		public boolean isSafe() {
			return true;
		}

		@Override
		public boolean isUnsafe() {
			return false;
		}

		@Override
		public Safe<S, A> asSafe() {
			return this;
		}

		@Override
		public Unsafe<S, A> asUnsafe() {
			throw new ClassCastException(
					"Cannot cast " + Safe.class.getSimpleName() + " to " + Unsafe.class.getSimpleName());
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(SafetyStatus.class.getSimpleName()).add(Safe.class.getSimpleName())
					.toString();
		}
	}

	public static final class Unsafe<S extends State, A extends Action> extends SafetyStatus<S, A> {
		private final Trace<S, A> cex;

		private Unsafe(final Trace<S, A> cex, final ARG<S, A> arg) {
			super(arg);
			this.cex = checkNotNull(cex);
		}

		public Trace<S, A> getTrace() {
			return cex;
		}

		@Override
		public boolean isSafe() {
			return false;
		}

		@Override
		public boolean isUnsafe() {
			return true;
		}

		@Override
		public Safe<S, A> asSafe() {
			throw new ClassCastException(
					"Cannot cast " + Unsafe.class.getSimpleName() + " to " + Safe.class.getSimpleName());
		}

		@Override
		public Unsafe<S, A> asUnsafe() {
			return this;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(SafetyStatus.class.getSimpleName()).add(Unsafe.class.getSimpleName())
					.toString();
		}
	}

}
