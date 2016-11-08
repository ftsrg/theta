package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.ObjectUtils.toStringBuilder;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

public final class ArgNode<S extends State, A extends Action> {

	final ARG<S, A> arg;

	private final int id;
	private final boolean target;

	private S state;

	Optional<ArgEdge<S, A>> inEdge;
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode;
	final Collection<ArgNode<S, A>> coveredNodes;

	boolean expanded;

	ArgNode(final ARG<S, A> arg, final S state, final int id, final boolean target) {
		this.arg = arg;
		this.state = state;
		this.id = id;
		this.target = target;
		inEdge = Optional.empty();
		outEdges = new HashSet<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
		expanded = false;
	}

	////

	public int getId() {
		return id;
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

	public Optional<ArgEdge<S, A>> getInEdge() {
		return inEdge;
	}

	public Collection<ArgEdge<S, A>> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	public Optional<ArgNode<S, A>> getCoveringNode() {
		return coveringNode;
	}

	public Collection<ArgNode<S, A>> getCoveredNodes() {
		return Collections.unmodifiableCollection(coveredNodes);
	}

	////

	public Stream<ArgNode<S, A>> getSuccNodes() {
		return outEdges.stream().map(ArgEdge::getTarget);
	}

	public Stream<S> getSuccStates() {
		return getSuccNodes().map(ArgNode::getState);
	}

	////

	public boolean isCovered() {
		if (coveringNode.isPresent()) {
			return true;
		} else if (inEdge.isPresent()) {
			return inEdge.get().getSource().isCovered();
		} else {
			return false;
		}
	}

	public boolean isTarget() {
		return target;
	}

	public boolean isLeaf() {
		return outEdges.isEmpty();
	}

	////

	public Optional<ArgNode<S, A>> parent() {
		if (inEdge.isPresent()) {
			return Optional.of(inEdge.get().getSource());
		} else {
			return Optional.empty();
		}
	}

	public Stream<ArgNode<S, A>> properAncestors() {
		final Optional<ArgNode<S, A>> parent = this.parent();
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

	public boolean isExpanded() {
		return expanded;
	}

	public boolean isFeasible(final Domain<S> domain) {
		return !domain.isBottom(state);
	}

	public boolean isSafe(final Domain<S> domain) {
		return !(isFeasible(domain) && isTarget());
	}

	public boolean isComplete() {
		return isExpanded() || isTarget() || isCovered();
	}

	@Override
	public int hashCode() {
		return super.hashCode();
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
