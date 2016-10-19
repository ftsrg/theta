package hu.bme.mit.theta.analysis.algorithm;

import static hu.bme.mit.theta.common.ObjectUtils.toStringBuilder;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public final class ArgNode<S extends State, A extends Action> {

	final ARG<S, A> arg;

	private final int id;
	private final S state;
	private final boolean target;

	Optional<ArgEdge<S, A>> inEdge;
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode;
	final Collection<ArgNode<S, A>> coveredNodes;

	ArgNode(final ARG<S, A> arg, final S state, final int id, final boolean target) {
		this.arg = arg;
		this.state = state;
		this.id = id;
		this.target = target;
		inEdge = Optional.empty();
		outEdges = new HashSet<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
	}

	////

	public int getId() {
		return id;
	}

	public S getState() {
		return state;
	}

	public boolean isTarget() {
		return target;
	}

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

	////

	public Collection<ArgNode<S, A>> getSuccNodes() {
		return outEdges.stream().map(ArgEdge::getTarget).collect(toList());
	}

	public Collection<S> getSuccStates() {
		return outEdges.stream().map(e -> e.getTarget().getState()).collect(toSet());
	}

	////

	public boolean mayCover(final ArgNode<S, A> that) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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

	////

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
