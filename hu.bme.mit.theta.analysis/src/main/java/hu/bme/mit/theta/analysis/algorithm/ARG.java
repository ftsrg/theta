package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

/**
 * Represents an abstract reachability graph (ARG).
 */
public final class ARG<S extends State, A extends Action> {

	private final Collection<ArgNode<S, A>> nodes;
	private final Collection<ArgEdge<S, A>> edges;

	private final Collection<ArgNode<S, A>> initNodes;
	private final Collection<ArgNode<S, A>> targetNodes;
	private final Collection<ArgNode<S, A>> leafNodes;

	private int nextId = 0;

	public ARG() {
		nodes = new LinkedHashSet<>();
		edges = new HashSet<>();
		initNodes = new HashSet<>();
		leafNodes = new HashSet<>();
		targetNodes = new HashSet<>();
	}

	////

	public Collection<ArgNode<S, A>> getNodes() {
		return Collections.unmodifiableCollection(nodes);
	}

	public Collection<ArgEdge<S, A>> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public Collection<ArgNode<S, A>> getInitNodes() {
		return Collections.unmodifiableCollection(initNodes);
	}

	public Collection<ArgNode<S, A>> getTargetNodes() {
		return Collections.unmodifiableCollection(targetNodes);
	}

	public Collection<ArgNode<S, A>> getLeafNodes() {
		return Collections.unmodifiableCollection(leafNodes);
	}

	////

	public boolean isComplete() {
		return leafNodes.stream().allMatch(ArgNode::isCovered);
	}

	public boolean isSafe(final Domain<S> domain) {
		return targetNodes.stream().map(ArgNode::getState).allMatch(domain::isBottom);
	}

	////

	public ArgNode<S, A> createInitNode(final S initState, final boolean target) {
		checkNotNull(initState);
		final ArgNode<S, A> initNode = createNode(initState, target);
		initNodes.add(initNode);
		leafNodes.add(initNode);
		return initNode;
	}

	public ArgNode<S, A> createSuccNode(final ArgNode<S, A> node, final A action, final S succState,
			final boolean target) {
		checkNotNull(node);
		checkNotNull(action);
		checkNotNull(succState);
		checkArgument(node.arg == this);
		checkArgument(!node.isTarget());
		final ArgNode<S, A> succNode = createNode(succState, target);
		createEdge(node, action, succNode);
		leafNodes.add(succNode);
		leafNodes.remove(node);
		return succNode;
	}

	////

	private ArgNode<S, A> createNode(final S state, final boolean target) {
		final ArgNode<S, A> node = new ArgNode<>(this, state, nextId, target);
		nodes.add(node);
		if (target) {
			targetNodes.add(node);
		}
		nextId = nextId + 1;
		return node;
	}

	private ArgEdge<S, A> createEdge(final ArgNode<S, A> source, final A action, final ArgNode<S, A> target) {
		final ArgEdge<S, A> edge = new ArgEdge<>(source, action, target);
		source.outEdges.add(edge);
		target.inEdge = Optional.of(edge);
		edges.add(edge);
		return edge;
	}

	////

	public Trace<S, A> getTraceTo(final ArgNode<S, A> node) {
		checkArgument(nodes.contains(node));

		final List<S> states = new ArrayList<>();
		final List<A> actions = new ArrayList<>();
		ArgNode<S, A> running = node;
		do {
			states.add(0, running.getState());
			if (running.getInEdge().isPresent()) {
				final ArgEdge<S, A> edge = running.getInEdge().get();
				actions.add(0, edge.getAction());
				running = edge.getSource();
			} else {
				running = null;
			}
		} while (running != null);
		return new Trace<>(states, actions);
	}

	/**
	 * Gets all counterexamples, i.e., traces leading to target states.
	 */
	public Collection<Trace<S, A>> getAllCexs() {
		final List<Trace<S, A>> cexs = new ArrayList<>();

		for (final ArgNode<S, A> targetNode : getTargetNodes()) {
			final Trace<S, A> trace = getTraceTo(targetNode);
			cexs.add(trace);
		}

		assert cexs.size() == getTargetNodes().size();
		return cexs;
	}

	/**
	 * Gets a single counterexample, i.e., a trace leading to a target state (if
	 * at least one target state exists in the ARG).
	 */
	public Optional<Trace<S, A>> getAnyCex() {
		if (getTargetNodes().size() == 0) {
			return Optional.empty();
		} else {
			final ArgNode<S, A> targetNode = getTargetNodes().iterator().next();
			return Optional.of(getTraceTo(targetNode));
		}
	}

}
