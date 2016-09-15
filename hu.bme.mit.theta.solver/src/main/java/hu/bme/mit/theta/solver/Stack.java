package hu.bme.mit.theta.solver;

import java.util.Collection;

public interface Stack<T> {

	public void add(final T elem);

	public void add(final Collection<? extends T> elems);

	public void push();

	public void pop(final int n);

	public default void pop() {
		pop(1);
	}

	public Collection<T> toCollection();

}
