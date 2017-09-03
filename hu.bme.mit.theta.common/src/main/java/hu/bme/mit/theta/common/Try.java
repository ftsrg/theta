package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Supplier;

public abstract class Try<T> {

	private Try() {
	}

	public static <T> Try<T> attempt(final Supplier<? extends T> supplier) {
		try {
			final T value = supplier.get();
			return success(value);
		} catch (final Exception exception) {
			return failure(exception);
		}
	}

	public static <T> Success<T> success(final T value) {
		return new Success<>(value);
	}

	public static <T> Failure<T> failure(final Exception exception) {
		return new Failure<>(exception);
	}

	public abstract boolean isSuccess();

	public abstract boolean isFailure();

	public abstract Success<T> asSuccess();

	public abstract Failure<T> asFailure();

	public static final class Success<T> extends Try<T> {
		private static final int HASH_SEED = 2851;
		private volatile int hashCode = 0;

		private final T value;

		private Success(final T value) {
			this.value = checkNotNull(value);
		}

		public T getValue() {
			return value;
		}

		@Override
		public boolean isSuccess() {
			return true;
		}

		@Override
		public boolean isFailure() {
			return false;
		}

		@Override
		public Success<T> asSuccess() {
			return this;
		}

		@Override
		public Failure<T> asFailure() {
			throw new ClassCastException();
		}

		@Override
		public final int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + value.hashCode();
				hashCode = result;
			}
			return hashCode;
		}

		@Override
		public final boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj == null) {
				return false;
			} else if (obj instanceof Success) {
				final Success<?> that = (Success<?>) obj;
				return this.value.equals(that.value);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return Utils.toStringBuilder("Success").add(value).toString();
		}
	}

	public static final class Failure<T> extends Try<T> {
		private static final int HASH_SEED = 4271;
		private volatile int hashCode = 0;

		private final Exception exception;

		private Failure(final Exception exception) {
			this.exception = checkNotNull(exception);
		}

		public Exception getException() {
			return exception;
		}

		public void raise() throws Exception {
			throw exception;
		}

		@Override
		public boolean isSuccess() {
			return false;
		}

		@Override
		public boolean isFailure() {
			return true;
		}

		@Override
		public Success<T> asSuccess() {
			throw new ClassCastException();
		}

		@Override
		public Failure<T> asFailure() {
			return this;
		}

		@Override
		public final int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + exception.hashCode();
				hashCode = result;
			}
			return hashCode;
		}

		@Override
		public final boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj == null) {
				return false;
			} else if (obj instanceof Failure) {
				final Failure<?> that = (Failure<?>) obj;
				return this.exception.equals(that.exception);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return Utils.toStringBuilder("Faliure").add(exception).toString();
		}
	}

}
