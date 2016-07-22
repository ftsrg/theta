package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

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

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.Trace;
import hu.bme.mit.inf.ttmc.analysis.impl.TraceImpl;

public class ARG<S extends State, A extends Action, P extends Precision> {

	private final Analysis<S, A, P> analysis;
	private final Predicate<? super S> target;

	private final Collection<ARGNode<S, A>> nodes;
	private final Collection<ARGEdge<S, A>> edges;

	private final Collection<ARGNode<S, A>> initNodes;
	private final Collection<ARGNode<S, A>> targetNodes;

	private int nextId = 0;

	ARG(final Analysis<S, A, P> analysis, final Predicate<? super S> target, final P precision) {
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
		nodes = new LinkedHashSet<>();
		edges = new HashSet<>();
		initNodes = new HashSet<>();
		targetNodes = new HashSet<>();
		init(precision);
	}

	////

	public Collection<ARGNode<S, A>> getNodes() {
		return Collections.unmodifiableCollection(nodes);
	}

	public Collection<ARGEdge<S, A>> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public Collection<ARGNode<S, A>> getInitNodes() {
		return Collections.unmodifiableCollection(initNodes);
	}

	public Collection<ARGNode<S, A>> getTargetNodes() {
		return Collections.unmodifiableCollection(targetNodes);
	}

	public Trace<S, A> getTraceTo(final ARGNode<S, A> node) {
		checkArgument(nodes.contains(node));

		final List<S> states = new ArrayList<>();
		final List<A> actions = new ArrayList<>();
		ARGNode<S, A> running = node;
		do {
			states.add(0, running.getState());
			if (running.getInEdge().isPresent()) {
				final ARGEdge<S, A> edge = running.getInEdge().get();
				actions.add(0, edge.getAction());
				running = edge.getSource();
			} else {
				running = null;
			}
		} while (running != null);
		return new TraceImpl<>(states, actions);
	}

	public Collection<Trace<S, A>> getCounterexamples() {
		final List<Trace<S, A>> counterexamples = new ArrayList<>();

		for (final ARGNode<S, A> targetNode : getTargetNodes()) {
			final Trace<S, A> trace = getTraceTo(targetNode);
			counterexamples.add(trace);
		}

		assert counterexamples.size() == getTargetNodes().size();
		return counterexamples;
	}

	////

	public void expand(final ARGNode<S, A> node, final P precision) {
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

	public void close(final ARGNode<S, A> node) {
		for (final ARGNode<S, A> nodeToCoverWith : nodes) {
			if (nodeToCoverWith.getId() >= node.getId()) {
				break;
			}
			cover(node, nodeToCoverWith);
		}
	}

	////

	private void cover(final ARGNode<S, A> nodeToCover, final ARGNode<S, A> nodeToCoverWith) {
		checkNotNull(nodeToCover);
		checkNotNull(nodeToCoverWith);
		checkArgument(nodes.contains(nodeToCover));
		checkArgument(nodes.contains(nodeToCoverWith));

		if (nodeToCover.isCovered() || nodeToCoverWith.existsAncestor(n -> nodeToCover.equals(n))) {
			return;
		}

		if (analysis.getDomain().isLeq(nodeToCover.getState(), nodeToCoverWith.getState())) {
			addCoveringEdge(nodeToCover, nodeToCoverWith);
			nodeToCover.foreachDescendants(ARGNode::clearCoveredNodes);
		}
	}

	private void init(final P precision) {
		checkNotNull(precision);

		final Collection<? extends S> initStates = analysis.getInitFunction().getInitStates(precision);
		for (final S initState : initStates) {
			final boolean isTarget = target.test(initState);
			createInitNode(initState, isTarget);
		}
	}

	private ARGNode<S, A> createInitNode(final S initState, final boolean target) {
		final ARGNode<S, A> initNode = createNode(initState, target);
		initNodes.add(initNode);
		return initNode;
	}

	private ARGNode<S, A> createSuccNode(final ARGNode<S, A> node, final A action, final S succState,
			final boolean target) {
		assert nodes.contains(node);

		final ARGNode<S, A> succNode = createNode(succState, target);
		createEdge(node, action, succNode);
		return succNode;
	}

	////

	private ARGEdge<S, A> createEdge(final ARGNode<S, A> source, final A action, final ARGNode<S, A> target) {
		final ARGEdge<S, A> edge = new ARGEdge<>(source, action, target);
		source.outEdges.add(edge);
		target.inEdge = Optional.of(edge);
		edges.add(edge);
		return edge;
	}

	private ARGNode<S, A> createNode(final S state, final boolean target) {
		final ARGNode<S, A> node = new ARGNode<>(state, nextId, target);
		nodes.add(node);
		if (node.isTarget()) {
			targetNodes.add(node);
		}
		nextId++;
		return node;
	}

	private void addCoveringEdge(final ARGNode<S, A> nodeToCover, final ARGNode<S, A> nodeToCoverWith) {
		nodeToCover.coveringNode = Optional.of(nodeToCoverWith);
		nodeToCoverWith.coveredNodes.add(nodeToCover);
	}

}
