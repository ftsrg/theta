package hu.bme.mit.theta.analysis.reachedset;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Stream;

public final class Partition<T, K> {

	private final Function<? super T, ? extends K> projection;
	private final Map<K, Collection<T>> classes;

	private Partition(final Function<? super T, ? extends K> projection) {
		this.projection = checkNotNull(projection);
		classes = new HashMap<>();
	}

	public static <T, K> Partition<T, K> of(final Function<? super T, ? extends K> projection) {
		return new Partition<>(projection);
	}

	public void add(final T elem) {
		checkNotNull(elem);
		final K key = projection.apply(elem);
		final Collection<T> partition = classes.computeIfAbsent(key, k -> new ArrayList<>());
		partition.add(elem);
	}

	public void addAll(final Iterable<? extends T> elems) {
		elems.forEach(this::add);
	}

	public void addAll(final Stream<? extends T> elems) {
		elems.forEach(this::add);
	}

	public Collection<T> get(final T elem) {
		checkNotNull(elem);
		final K key = projection.apply(elem);
		final Collection<T> partition = classes.getOrDefault(key, Collections.emptyList());
		return partition;
	}

}
