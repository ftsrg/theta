package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.ObjectUtils.toStringBuilder;
import static hu.bme.mit.theta.common.Utils.anyMatch;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public final class ArgNode<S extends State, A extends Action> {

	private static final int HASH_SEED = 8543;
	private volatile int hashCode = 0;

	final ARG<S, A> arg;

	private final int id;
	private final int depth;
	private final boolean target;

	private S state;

	Optional<ArgEdge<S, A>> inEdge; // Set by ARG
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode; // Set by ARG
	final Collection<ArgNode<S, A>> coveredNodes;

	boolean expanded; // Set by ArgBuilder

	ArgNode(final ARG<S, A> arg, final S state, final int id, final int depth, final boolean target) {
		this.arg = arg;
		this.state = state;
		this.id = id;
		this.depth = depth;
		this.target = target;
		inEdge = Optional.empty();
		outEdges = new ArrayList<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
		expanded = false;
	}

	////

	public int getId() {
		return id;
	}

	/**
	 * Gets the depth of the node, which is 0 if the node has no parent, and
	 * depth(parent) + 1 otherwise.
	 */
	public int getDepth() {
		return depth;
	}

	public S getState() {
		return state;
	}

	public void setState(final S state) {
		checkNotNull(state);
		this.state = state;
	}

	public void clearCoveredNodes() {
		coveredNodes.forEach(n -> n.coveringNode = Optional.empty());
		coveredNodes.clear();
	}

	////

	public Optional<ArgNode<S, A>> getParent() {
		return inEdge.map(ArgEdge::getSource);
	}

	public Optional<ArgEdge<S, A>> getInEdge() {
		return inEdge;
	}

	public Stream<ArgEdge<S, A>> getOutEdges() {
		return outEdges.stream();
	}

	public Optional<ArgNode<S, A>> getCoveringNode() {
		return coveringNode;
	}

	public Stream<ArgNode<S, A>> getCoveredNodes() {
		return coveredNodes.stream();
	}

	////

	public Stream<ArgNode<S, A>> getSuccNodes() {
		return getOutEdges().map(ArgEdge::getTarget);
	}

	public Stream<S> getSuccStates() {
		return getSuccNodes().map(ArgNode::getState);
	}

	////

	/**
	 * Checks if the node is excluded, i.e., the node is covered or not feasible
	 * or has an excluded parent.
	 */
	public boolean isExcluded() {
		return isCovered() || !isFeasible() || anyMatch(getParent(), ArgNode::isExcluded);
	}

	/**
	 * Checks if the node is covered, i.e., there is a covering edge for the
	 * node.
	 */
	private boolean isCovered() {
		return coveringNode.isPresent();
	}

	/**
	 * Checks if the node is target, i.e., the target predicate holds (e.g., it
	 * is an error state).
	 */
	public boolean isTarget() {
		return target;
	}

	/**
	 * Checks if the node is expanded, i.e., all of its successors are present.
	 */
	public boolean isExpanded() {
		return expanded;
	}

	/**
	 * Checks if the node is not a bottom state.
	 */
	public boolean isFeasible() {
		return !arg.domain.isBottom(state);
	}

	/**
	 * Checks if the node is safe, i.e., not target or covered.
	 */
	public boolean isSafe() {
		return !isTarget() || isExcluded();
	}

	/**
	 * Checks if the node is complete, i.e., expanded or target or covered.
	 */
	public boolean isComplete() {
		return isExpanded() || isTarget() || isExcluded();
	}

	////

	public Stream<ArgNode<S, A>> properAncestors() {
		final Optional<ArgNode<S, A>> parent = getParent();
		if (parent.isPresent()) {
			return Stream.concat(Stream.of(parent.get()), parent.get().properAncestors());
		} else {
			return Stream.empty();
		}
	}

	public Stream<ArgNode<S, A>> ancestors() {
		return Stream.concat(Stream.of(this), this.properAncestors());
	}

	public Stream<ArgNode<S, A>> children() {
		return outEdges.stream().map(e -> e.getTarget());
	}

	public Stream<ArgNode<S, A>> properDescendants() {
		return Stream.concat(this.children(), this.children().flatMap(ArgNode::properDescendants));
	}

	public Stream<ArgNode<S, A>> descendants() {
		return Stream.concat(Stream.of(this), this.properDescendants());
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + id;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return super.equals(obj);
	}

	@Override
	public String toString() {
		return toStringBuilder("ArgNode").add(id).add(state).toString();
	}

}
