package hu.bme.mit.theta.analysis.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.Utils;

public final class RandomWaitlist<T> implements Waitlist<T> {

	private final List<T> items;
	private final Random random;

	private RandomWaitlist() {
		items = new LinkedList<>();
		random = new Random();
	}

	public static <T> RandomWaitlist<T> create() {
		return new RandomWaitlist<>();
	}

	@Override
	public void add(final T item) {
		checkNotNull(item);
		items.add(item);
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		checkNotNull(items);
		items.forEach(i -> this.items.add(i));
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		checkNotNull(items);
		items.forEach(i -> this.items.add(i));
	}

	@Override
	public boolean isEmpty() {
		return items.isEmpty();
	}

	@Override
	public T remove() {
		final int i = random.nextInt(items.size());
		return items.remove(i);
	}

	@Override
	public int size() {
		return items.size();
	}

	@Override
	public void clear() {
		items.clear();
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).addAll(items).toString();
	}

}
