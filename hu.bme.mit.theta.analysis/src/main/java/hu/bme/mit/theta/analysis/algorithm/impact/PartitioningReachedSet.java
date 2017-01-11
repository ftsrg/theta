package hu.bme.mit.theta.analysis.algorithm.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

public final class PartitioningReachedSet<S extends State, A extends Action, K> extends AbstractReachedSet<S, A> {

	private final Function<? super S, ? extends K> partitioning;

	private final Map<K, Collection<ArgNode<S, A>>> partitions;

	private PartitioningReachedSet(final Function<? super S, ? extends K> partitioning) {
		this.partitioning = checkNotNull(partitioning);
		partitions = new HashMap<>();
	}

	public static <S extends State, A extends Action, K> PartitioningReachedSet<S, A, K> create(
			final Function<? super S, ? extends K> partitioning) {
		return new PartitioningReachedSet<>(partitioning);
	}

	@Override
	public void add(final ArgNode<S, A> node) {
		checkNotNull(node);
		final S state = node.getState();
		final K key = partitioning.apply(state);
		final Collection<ArgNode<S, A>> partition = partitions.computeIfAbsent(key, k -> new ArrayList<>());
		partition.add(node);
	}

	@Override
	protected Collection<? extends ArgNode<S, A>> getCandidatesForCovering(final ArgNode<S, A> node) {
		checkNotNull(node);
		final S state = node.getState();
		final K key = partitioning.apply(state);
		final Collection<ArgNode<S, A>> partition = partitions.getOrDefault(key, Collections.emptySet());
		return Collections.unmodifiableCollection(partition);
	}

}
