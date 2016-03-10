package hu.bme.mit.inf.ttmc.common.impl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import hu.bme.mit.inf.ttmc.common.Stack;


public class StackImpl<T> implements Stack<T> {

	public final LinkedList<T> stack;
	private final LinkedList<Integer> sizes;
	
	public StackImpl() {
		stack = new LinkedList<>();
		sizes = new LinkedList<>();
		sizes.add(0);
	}
	
	@Override
	public void add(T elem) {
		stack.add(elem);
	}

	@Override
	public void add(Collection<? extends T> elems) {
		stack.addAll(elems);
	}

	@Override
	public void push() {
		sizes.add(stack.size());
	}

	@Override
	public void pop(int n) {
		final int depth = sizes.size();
		checkArgument(depth > n);

		sizes.subList(depth - n, depth).clear();
		final int size = sizes.getLast();
		stack.subList(size, stack.size()).clear();
	}

	@Override
	public Collection<T> toCollection() {
		return Collections.unmodifiableCollection(stack);
	}

}
