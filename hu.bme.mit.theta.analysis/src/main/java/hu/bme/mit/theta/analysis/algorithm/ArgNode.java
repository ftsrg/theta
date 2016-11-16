package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.ObjectUtils.toStringBuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
	private final boolean target;

	private S state;

	Optional<ArgEdge<S, A>> inEdge;
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode;
	final Collection<ArgNode<S, A>> coveredNodes;

	boolean expanded;

	private volatile int depth;

	ArgNode(final ARG<S, A> arg, final S state, final int id, final boolean target) {
		this.arg = arg;
		this.state = state;
		this.id = id;
		this.target = target;
		inEdge = Optional.empty();
		outEdges = new ArrayList<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
		expanded = false;
		this.depth = -1;
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
		if (coveringNode.isPresent() || !isFeasible()) {
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

	public boolean isFeasible() {
		return !arg.domain.isBottom(state);
	}

	public boolean isSafe() {
		return !isTarget() || isCovered();
	}

	public boolean isComplete() {
		return isExpanded() || isTarget() || isCovered();
	}

	public int getDepth() {
		int result = depth;

		if (result == -1) {
			if (inEdge.isPresent()) {
				result = inEdge.get().getSource().getDepth() + 1;
			} else {
				result = 1;
			}
		}

		return result;
	}

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
