package hu.bme.mit.inf.theta.analysis.algorithm.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Predicate;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.State;

public final class ArgNode<S extends State, A extends Action> {

	private final int id;
	private final S state;
	private final boolean target;

	boolean expanded;

	Optional<ArgEdge<S, A>> inEdge;
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode;
	final Collection<ArgNode<S, A>> coveredNodes;

	ArgNode(final S state, final int id, final boolean target) {
		this.state = state;
		this.id = id;
		this.target = target;
		expanded = false;
		inEdge = Optional.empty();
		outEdges = new HashSet<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
	}

	////

	void clearCoveredNodes() {
		for (final ArgNode<S, A> coveredNode : coveredNodes) {
			coveredNode.coveringNode = Optional.empty();
		}
		coveredNodes.clear();
	}

	////

	public boolean existsAncestor(final Predicate<ArgNode<S, A>> predicate) {
		if (predicate.test(this)) {
			return true;
		} else if (inEdge.isPresent()) {
			return inEdge.get().getSource().existsAncestor(predicate);
		} else {
			return false;
		}
	}

	////

	public void foreachAncestors(final Consumer<ArgNode<S, A>> consumer) {
		consumer.accept(this);
		if (inEdge.isPresent()) {
			inEdge.get().getSource().foreachAncestors(consumer);
		}
	}

	public void foreachDescendants(final Consumer<ArgNode<S, A>> consumer) {
		consumer.accept(this);
		for (final ArgEdge<S, A> outEdge : outEdges) {
			outEdge.getTarget().foreachDescendants(consumer);
		}
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

	public Collection<ArgNode<S, A>> coveredNodes() {
		return Collections.unmodifiableCollection(coveredNodes);
	}

	public boolean isCovered() {
		if (coveringNode.isPresent()) {
			return true;
		} else if (inEdge.isPresent()) {
			return inEdge.get().getSource().isCovered();
		} else {
			return false;
		}
	}

	public int getId() {
		return id;
	}

	public S getState() {
		return state;
	}

	public boolean isTarget() {
		return target;
	}

	public boolean isExpanded() {
		return expanded;
	}

	////

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("ARGNode(");
		sb.append(state);
		sb.append(")");
		return sb.toString();
	}

	////

}
