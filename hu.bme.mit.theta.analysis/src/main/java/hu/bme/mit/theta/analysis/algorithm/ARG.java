package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

/**
 * Represents an abstract reachability graph (ARG).
 */
public final class ARG<S extends State, A extends Action> {

	private final Collection<ArgNode<S, A>> initNodes;

	boolean initialized;

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

	public Stream<ArgNode<S, A>> getNodes() {
		return getInitNodes().flatMap(ArgNode::descendants);
	}

	public Stream<ArgNode<S, A>> getInitNodes() {
		return initNodes.stream();
	}

	public Stream<ArgNode<S, A>> getUnsafeNodes() {
		return getNodes().filter(n -> !n.isSafe());
	}

	public Stream<ArgNode<S, A>> getIncompleteNodes() {
		return getNodes().filter(n -> !n.isComplete());
	}

	////

	public boolean isComplete() {
		return isInitialized() && getNodes().allMatch(ArgNode::isComplete);
	}

	public boolean isSafe() {
		// TODO: the current implementetion is only the definition of "safe".
		// More efficient implementation can be done by checking if all states
		// in the "targetNodes" collection are not feasible.
		return getNodes().allMatch(n -> n.isSafe());
	}

	public boolean isInitialized() {
		return initialized;
	}

	////

	public ArgNode<S, A> createInitNode(final S initState, final boolean target) {
		checkNotNull(initState);
		final ArgNode<S, A> initNode = createNode(initState, target);
		initNodes.add(initNode);
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
		node.descendants().forEach(this::uncover);
		node.descendants().forEach(ArgNode::clearCoveredNodes);

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
	 * Gets all counterexamples, i.e., traces leading to target states.
	 */
	public Stream<ArgTrace<S, A>> getCexs() {
		return getUnsafeNodes().map(n -> ArgTrace.to(n));
	}
}
