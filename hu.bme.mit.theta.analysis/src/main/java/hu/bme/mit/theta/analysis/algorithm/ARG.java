package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.anyElementOf;

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

/**
 * Represents an abstract reachability graph (ARG).
 */
public final class ARG<S extends State, A extends Action> {

	private final Collection<ArgNode<S, A>> nodes;

	private final Collection<ArgNode<S, A>> initNodes;
	private final Collection<ArgNode<S, A>> targetNodes;
	private final Collection<ArgNode<S, A>> leafNodes;

	private int nextId = 0;

	private ARG() {
		nodes = new LinkedHashSet<>();
		initNodes = new HashSet<>();
		leafNodes = new HashSet<>();
		targetNodes = new HashSet<>();
	}

	public static <S extends State, A extends Action> ARG<S, A> create() {
		return new ARG<>();
	}

	////

	public Collection<ArgNode<S, A>> getNodes() {
		return Collections.unmodifiableCollection(nodes);
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

	/**
	 * Removes a node along with its subtree
	 *
	 * @param node
	 */
	public void prune(final ArgNode<S, A> node) {
		checkNotNull(node);
		checkArgument(node.arg == this);

		for (final ArgNode<S, A> succ : node.getSuccNodes()) {
			prune(succ);
		}

		assert node.getOutEdges().size() == 0;

		nodes.remove(node);
		targetNodes.remove(node);
		leafNodes.remove(node);
		initNodes.remove(node);

		if (node.getInEdge().isPresent()) {
			final ArgEdge<S, A> edge = node.getInEdge().get();
			final ArgNode<S, A> parent = edge.getSource();
			parent.outEdges.remove(edge);
			if (parent.outEdges.size() == 0) {
				leafNodes.add(parent);
			}
		}

		if (node.getCoveringNode().isPresent()) {
			final ArgNode<S, A> coverer = node.getCoveringNode().get();
			coverer.coveredNodes.remove(node);
		}

	}

	public void cover(final ArgNode<S, A> node, final ArgNode<S, A> coveringNode) {
		checkNotNull(node);
		checkNotNull(coveringNode);
		checkArgument(node.arg == this);
		checkArgument(coveringNode.arg == this);
		checkArgument(!node.coveringNode.isPresent());
		node.coveringNode = Optional.of(coveringNode);
		coveringNode.coveredNodes.add(node);
	}

	public void uncover(final ArgNode<S, A> node) {
		checkNotNull(node);
		checkArgument(node.arg == this);
		if (node.coveringNode.isPresent()) {
			node.coveringNode.get().coveredNodes.remove(node);
			node.coveringNode = Optional.empty();
		}
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
		return edge;
	}

	////

	public ArgTrace<S, A> getTraceTo(final ArgNode<S, A> node) {
		checkArgument(nodes.contains(node));
		final List<ArgEdge<S, A>> edges = new ArrayList<>();

		ArgNode<S, A> target = node;
		while (target.inEdge.isPresent()) {
			final ArgEdge<S, A> edge = target.inEdge.get();
			edges.add(0, edge);
			target = edge.getSource();
		}

		if (edges.isEmpty()) {
			return ArgTrace.of(node);
		} else {
			return ArgTrace.of(edges);
		}
	}

	/**
	 * Gets all counterexamples, i.e., traces leading to target states.
	 */
	public Collection<ArgTrace<S, A>> getAllCexs() {
		final List<ArgTrace<S, A>> cexs = new ArrayList<>();

		for (final ArgNode<S, A> targetNode : getTargetNodes()) {
			final ArgTrace<S, A> trace = getTraceTo(targetNode);
			cexs.add(trace);
		}

		assert cexs.size() == getTargetNodes().size();
		return cexs;
	}

	/**
	 * Gets a single counterexample, i.e., a trace leading to a target state (if
	 * at least one target state exists in the ARG).
	 */
	public Optional<ArgTrace<S, A>> getAnyCex() {
		if (getTargetNodes().size() == 0) {
			return Optional.empty();
		} else {
			final ArgNode<S, A> targetNode = anyElementOf(targetNodes);
			return Optional.of(getTraceTo(targetNode));
		}
	}

}
