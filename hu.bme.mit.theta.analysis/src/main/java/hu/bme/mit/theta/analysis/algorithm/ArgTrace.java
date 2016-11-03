package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public final class ArgTrace<S extends State, A extends Action> implements Iterable<ArgNode<S, A>> {

	private final List<ArgNode<S, A>> nodes;
	private final List<ArgEdge<S, A>> edges;

	private ArgTrace(final ArgNode<S, A> node, final List<? extends ArgEdge<S, A>> edges) {
		checkTrace(node, edges);
		this.edges = ImmutableList.copyOf(edges);
		nodes = extractNodes(node, edges);
	}

	private static <S extends State, A extends Action> void checkTrace(final ArgNode<S, A> node,
			final List<? extends ArgEdge<S, A>> edges) {
		ArgNode<S, A> source = node;
		for (final ArgEdge<S, A> edge : edges) {
			checkArgument(edge.getSource() == source);
			source = edge.getTarget();
		}
	}

	private static <S extends State, A extends Action> List<ArgNode<S, A>> extractNodes(final ArgNode<S, A> node,
			final List<? extends ArgEdge<S, A>> edges) {
		final ImmutableList.Builder<ArgNode<S, A>> builder = ImmutableList.builder();
		builder.add(node);
		for (final ArgEdge<S, A> edge : edges) {
			builder.add(edge.getTarget());
		}
		return builder.build();
	}

	////

	public static <S extends State, A extends Action> ArgTrace<S, A> of(final ArgNode<S, A> node) {
		checkNotNull(node);
		return new ArgTrace<>(node, Collections.emptyList());
	}

	public static <S extends State, A extends Action> ArgTrace<S, A> of(final List<? extends ArgEdge<S, A>> edges) {
		checkNotNull(edges);
		checkArgument(!edges.isEmpty());
		return new ArgTrace<>(edges.get(0).getSource(), edges);
	}

	////

	public ArgNode<S, A> node(final int index) {
		return nodes.get(index);
	}

	public ArgEdge<S, A> edge(final int index) {
		return edges.get(index);
	}

	public List<ArgNode<S, A>> nodes() {
		return nodes;
	}

	public List<ArgEdge<S, A>> edges() {
		return edges;
	}

	////

	public Trace<S, A> toTrace() {
		final List<S> states = nodes.stream().map(ArgNode::getState).collect(toList());
		final List<A> actions = edges.stream().map(ArgEdge::getAction).collect(toList());
		return Trace.create(states, actions);
	}

	////

	@Override
	public Iterator<ArgNode<S, A>> iterator() {
		return nodes.iterator();
	}

	////

}
