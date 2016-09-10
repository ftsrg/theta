package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.NoSuchElementException;

public abstract class Either<L, R> {

	private Either() {
	}

	public static <L> Left<L, ?> Left(final L left) {
		return new Left<>(left);
	}

	public static <R> Right<?, R> Right(final R right) {
		return new Right<>(right);
	}

	public abstract boolean isLeft();

	public abstract boolean isRight();

	public abstract L left();

	public abstract R right();

	////

	public static final class Left<L, R> extends Either<L, R> {

		private static final int HASH_SEED = 6427;
		private volatile int hashCode = 0;

		private final L left;

		private Left(final L left) {
			this.left = checkNotNull(left);
		}

		@Override
		public boolean isLeft() {
			return true;
		}

		@Override
		public boolean isRight() {
			return false;
		}

		@Override
		public L left() {
			return left;
		}

		@Override
		public R right() {
			throw new NoSuchElementException();
		}

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + left.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof Left) {
				final Left<?, ?> that = (Left<?, ?>) obj;
				return this.left.equals(that.left);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return "Left(" + left + ")";
		}

	}

	public static final class Right<L, R> extends Either<L, R> {

		private static final int HASH_SEED = 4801;
		private volatile int hashCode = 0;

		private final R right;

		private Right(final R right) {
			this.right = checkNotNull(right);
		}

		@Override
		public boolean isLeft() {
			return false;
		}

		@Override
		public boolean isRight() {
			return true;
		}

		@Override
		public L left() {
			throw new NoSuchElementException();
		}

		@Override
		public R right() {
			return right;
		}

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + right.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof Right) {
				final Right<?, ?> that = (Right<?, ?>) obj;
				return this.right.equals(that.right);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return "Right(" + right + ")";
		}

	}

}
