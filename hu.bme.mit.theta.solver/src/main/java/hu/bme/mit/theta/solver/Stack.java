package hu.bme.mit.theta.solver;

import java.util.Collection;

public interface Stack<T> extends Iterable<T> {

	void add(final T elem);

	void add(final Collection<? extends T> elems);

	void push();

	void pop(final int n);

	default void pop() {
		pop(1);
	}

	Collection<T> toCollection();

}
