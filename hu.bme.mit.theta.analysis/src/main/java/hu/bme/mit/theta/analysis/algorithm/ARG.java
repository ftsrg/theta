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
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public final class ARG<S extends State, A extends Action, P extends Precision> {

	private final Analysis<S, A, P> analysis;
	private final Predicate<? super S> target;

	private final Collection<ArgNode<S, A>> nodes;
	private final Collection<ArgEdge<S, A>> edges;

	private final Collection<ArgNode<S, A>> initNodes;
	private final Collection<ArgNode<S, A>> leafNodes;
	private final Collection<ArgNode<S, A>> targetNodes;

	private int nextId = 0;

	public ARG(final Analysis<S, A, P> analysis, final Predicate<? super S> target, final P precision) {
		checkNotNull(analysis);
		checkNotNull(target);
		checkNotNull(precision);
		this.analysis = analysis;
		this.target = target;
		nodes = new LinkedHashSet<>();
		edges = new HashSet<>();
		initNodes = new HashSet<>();
		leafNodes = new HashSet<>();
		targetNodes = new HashSet<>();
		init(precision);
	}

	////

	public boolean isComplete() {
		return leafNodes.stream().allMatch(ArgNode::isCovered);
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

	public Collection<ArgNode<S, A>> getLeafNodes() {
		return Collections.unmodifiableCollection(leafNodes);
	}

	public Collection<ArgNode<S, A>> getTargetNodes() {
		return Collections.unmodifiableCollection(targetNodes);
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

	public Collection<Trace<S, A>> getCounterexamples() {
		final List<Trace<S, A>> counterexamples = new ArrayList<>();

		for (final ArgNode<S, A> targetNode : getTargetNodes()) {
			final Trace<S, A> trace = getTraceTo(targetNode);
			counterexamples.add(trace);
		}

		assert counterexamples.size() == getTargetNodes().size();
		return counterexamples;
	}

	////

	public void expand(final ArgNode<S, A> node, final P precision) {
		checkNotNull(node);
		checkNotNull(precision);
		checkArgument(nodes.contains(node));

		if (node.isExpanded() || analysis.getDomain().isBottom(node.getState())) {
			return;
		}

		final S state = node.getState();
		final Collection<? extends A> actions = analysis.getActionFunction().getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> succStates = analysis.getTransferFunction().getSuccStates(state, action,
					precision);
			for (final S succState : succStates) {
				final boolean isTarget = target.test(succState);
				createSuccNode(node, action, succState, isTarget);
			}
		}

		node.expanded = true;
	}

	public void close(final ArgNode<S, A> node) {
		for (final ArgNode<S, A> nodeToCoverWith : nodes) {
			if (nodeToCoverWith.getId() >= node.getId()) {
				break;
			}
			cover(node, nodeToCoverWith);
		}
	}

	////

	private void cover(final ArgNode<S, A> nodeToCover, final ArgNode<S, A> nodeToCoverWith) {
		checkNotNull(nodeToCover);
		checkNotNull(nodeToCoverWith);
		checkArgument(nodes.contains(nodeToCover));
		checkArgument(nodes.contains(nodeToCoverWith));

		if (nodeToCover.isCovered() || nodeToCoverWith.existsAncestor(n -> nodeToCover.equals(n))) {
			return;
		}

		if (analysis.getDomain().isLeq(nodeToCover.getState(), nodeToCoverWith.getState())) {
			addCoveringEdge(nodeToCover, nodeToCoverWith);
			nodeToCover.foreachDescendants(ArgNode::clearCoveredNodes);
		}
	}

	private void init(final P precision) {
		final Collection<? extends S> initStates = analysis.getInitFunction().getInitStates(precision);
		for (final S initState : initStates) {
			final boolean isTarget = target.test(initState);
			createInitNode(initState, isTarget);
		}
	}

	private void createInitNode(final S initState, final boolean target) {
		final ArgNode<S, A> initNode = createNode(initState, target);
		initNodes.add(initNode);
	}

	private ArgNode<S, A> createSuccNode(final ArgNode<S, A> node, final A action, final S succState,
			final boolean target) {
		assert nodes.contains(node);
		final ArgNode<S, A> succNode = createNode(succState, target);
		createEdge(node, action, succNode);
		return succNode;
	}

	////

	private ArgNode<S, A> createNode(final S state, final boolean target) {
		final ArgNode<S, A> node = new ArgNode<>(state, nextId, target);
		nodes.add(node);
		leafNodes.add(node);
		if (node.isTarget()) {
			targetNodes.add(node);
		}
		nextId = nextId + 1;
		return node;
	}

	private ArgEdge<S, A> createEdge(final ArgNode<S, A> source, final A action, final ArgNode<S, A> target) {
		final ArgEdge<S, A> edge = new ArgEdge<>(source, action, target);
		source.outEdges.add(edge);
		target.inEdge = Optional.of(edge);
		leafNodes.remove(source);
		edges.add(edge);
		return edge;
	}

	private void addCoveringEdge(final ArgNode<S, A> nodeToCover, final ArgNode<S, A> nodeToCoverWith) {
		nodeToCover.coveringNode = Optional.of(nodeToCoverWith);
		nodeToCoverWith.coveredNodes.add(nodeToCover);
	}

}
