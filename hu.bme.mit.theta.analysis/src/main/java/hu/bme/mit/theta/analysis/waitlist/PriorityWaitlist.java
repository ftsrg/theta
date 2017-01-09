package hu.bme.mit.theta.analysis.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Comparator;
import java.util.PriorityQueue;
import java.util.function.Supplier;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * Priority waitlist. The least item is always removed based on a comaprator or
 * on the natural ordering (if no comparator is given).
 */
public final class PriorityWaitlist<T> implements Waitlist<T> {

	private final PriorityQueue<T> items;

	private PriorityWaitlist(final Comparator<? super T> comparator) {
		items = new PriorityQueue<>(checkNotNull(comparator));
	}

	private PriorityWaitlist() {
		items = new PriorityQueue<>();
	}

	public static <T> PriorityWaitlist<T> create(final Comparator<? super T> comparator) {
		return new PriorityWaitlist<>(comparator);
	}

	public static <T> PriorityWaitlist<T> create() {
		return new PriorityWaitlist<>();
	}

	@Override
	public void add(final T item) {
		items.add(item);
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		checkNotNull(items);
		items.forEach(this::add);
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		checkNotNull(items);
		items.forEach(this::add);
	}

	@Override
	public boolean isEmpty() {
		return items.isEmpty();
	}

	@Override
	public T remove() {
		return items.remove();
	}

	@Override
	public int size() {
		return items.size();
	}

	@Override
	public void clear() {
		items.clear();
	}

	public static <T> Supplier<PriorityWaitlist<T>> supplier(final Comparator<? super T> comparator) {
		return () -> PriorityWaitlist.create(comparator);
	}

	public static <T> Supplier<PriorityWaitlist<T>> supplier() {
		return PriorityWaitlist::create;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("PriorityWaitlist").add(items.comparator()).addAll(items).toString();
	}
}
