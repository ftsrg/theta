package hu.bme.mit.theta.common;

import java.util.Comparator;
import java.util.Objects;

@FunctionalInterface
public interface TernaryOperator<T> extends TriFunction<T, T, T, T> {

	public static <T> TernaryOperator<T> minBy(final Comparator<? super T> comparator) {
		Objects.requireNonNull(comparator);
		return (a, b, c) -> comparator.compare(a, b) <= 0 ? (comparator.compare(a, c) <= 0 ? a : c)
				: (comparator.compare(b, c) <= 0 ? b : c);
	}

	public static <T> TernaryOperator<T> maxBy(final Comparator<? super T> comparator) {
		Objects.requireNonNull(comparator);
		return (a, b, c) -> comparator.compare(a, b) >= 0 ? (comparator.compare(a, c) >= 0 ? a : c)
				: (comparator.compare(b, c) >= 0 ? b : c);
	}

}
