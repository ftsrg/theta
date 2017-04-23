package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

/**
 * Represents an abstract reachability graph (ARG).
 */
public final class ARG<S extends State, A extends Action> {

	private final Collection<ArgNode<S, A>> initNodes;
	boolean initialized; // Set by ArgBuilder
	private int nextId = 0;
	final Domain<S> domain;

	private ARG(final Domain<S> domain) {
		initNodes = new HashSet<>();
		this.domain = domain;
		this.initialized = false;
	}

	public static <S extends State, A extends Action> ARG<S, A> create(final Domain<S> domain) {
		return new ARG<>(domain);
	}

	////

	public Stream<ArgNode<S, A>> getInitNodes() {
		return initNodes.stream();
	}

	public Stream<S> getInitStates() {
		return getInitNodes().map(ArgNode::getState);
	}

	public Stream<ArgNode<S, A>> getNodes() {
		return getInitNodes().flatMap(ArgNode::descendants);
	}

	public Stream<ArgNode<S, A>> getUnsafeNodes() {
		return getInitNodes().flatMap(ArgNode::unexcludedDescendants).filter(n -> n.isTarget());
	}

	public Stream<ArgNode<S, A>> getIncompleteNodes() {
		return getInitNodes().flatMap(ArgNode::unexcludedDescendants).filter(n -> !n.isExpanded());
	}

	////

	/**
	 * Checks if the ARG is complete, i.e., whether it is initialized and all of
	 * its nodes are complete.
	 */
	public boolean isComplete() {
		return isInitialized() && getNodes().allMatch(ArgNode::isComplete);
	}

	/**
	 * Checks if the ARG is safe, i.e., whether all of its nodes are safe.
	 */
	public boolean isSafe() {
		return getNodes().allMatch(n -> n.isSafe());
	}

	/**
	 * Checks if the ARG is initialized, i.e., all of its initial nodes are
	 * present.
	 */
	public boolean isInitialized() {
		return initialized;
	}

	////

	public ArgNode<S, A> createInitNode(final S initState, final boolean target) {
		checkNotNull(initState);
		final ArgNode<S, A> initNode = createNode(initState, 0, target);
		initNodes.add(initNode);
		return initNode;
	}

	public ArgNode<S, A> createSuccNode(final ArgNode<S, A> node, final A action, final S succState,
			final boolean target) {
		checkNotNull(node);
		checkNotNull(action);
		checkNotNull(succState);
		checkArgument(node.arg == this, "Node does not belong to this ARG");
		checkArgument(!node.isTarget(), "Node is target");
		final ArgNode<S, A> succNode = createNode(succState, node.getDepth() + 1, target);
		createEdge(node, action, succNode);
		return succNode;
	}

	private ArgNode<S, A> createNode(final S state, final int depth, final boolean target) {
		final ArgNode<S, A> node = new ArgNode<>(this, state, nextId, depth, target);
		nextId = nextId + 1;
		return node;
	}

	private ArgEdge<S, A> createEdge(final ArgNode<S, A> source, final A action, final ArgNode<S, A> target) {
		final ArgEdge<S, A> edge = new ArgEdge<>(source, action, target);
		source.outEdges.add(edge);
		target.inEdge = Optional.of(edge);
		return edge;
	}

	/**
	 * Removes a node along with its subtree.
	 */
	public void prune(final ArgNode<S, A> node) {
		checkNotNull(node);
		checkArgument(node.arg == this, "Node does not belong to this ARG");
		if (node.getInEdge().isPresent()) {
			final ArgEdge<S, A> edge = node.getInEdge().get();
			final ArgNode<S, A> parent = edge.getSource();
			parent.outEdges.remove(edge);
			parent.expanded = false;
		} else {
			assert initNodes.contains(node);
			initNodes.remove(node);
			this.initialized = false;
		}
		node.descendants().forEach(ArgNode::unsetCoveringNode);
		node.descendants().forEach(ArgNode::clearCoveredNodes);

	}

	public void minimize() {
		initNodes.forEach(this::minimizeSubTree);
	}

	private void minimizeSubTree(final ArgNode<S, A> node) {
		final Stream<ArgNode<S, A>> children = node.children().collect(toList()).stream();
		if (node.isExcluded()) {
			children.forEach(this::prune);
		} else {
			children.forEach(this::minimizeSubTree);
		}
	}

	////

	/**
	 * Gets all counterexamples, i.e., traces leading to target nodes.
	 */
	public Stream<ArgTrace<S, A>> getCexs() {
		return getUnsafeNodes().map(n -> ArgTrace.to(n));
	}

	/**
	 * Gets the size of the ARG, i.e., the number of nodes.
	 */
	public long size() {
		return getNodes().count();
	}

	/**
	 * Gets the depth of the ARG, i.e., the maximal depth of its nodes. Depth
	 * starts (at the initial nodes) from 0. Depth is undefined for an empty
	 * ARG.
	 */
	public int getDepth() {
		final OptionalInt maxOpt = getNodes().mapToInt(ArgNode::getDepth).max();
		checkState(maxOpt.isPresent(), "Depth is undefined for an empty ARG.");
		return maxOpt.getAsInt();
	}

	/**
	 * Gets the mean branching factor of the expanded nodes.
	 */
	public double getMeanBranchingFactor() {
		final Stream<ArgNode<S, A>> nodesToCalculate = getNodes().filter(n -> n.isExpanded());
		final double mean = nodesToCalculate.mapToDouble(n -> n.getOutEdges().count()).average().orElse(0);
		return mean;
	}

}
