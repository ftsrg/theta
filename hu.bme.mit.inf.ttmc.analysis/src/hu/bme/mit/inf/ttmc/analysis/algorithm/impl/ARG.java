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

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.impl.CounterexampleImpl;

public class ARG<S extends State, A extends Action> {

	private final Domain<S> domain;

	private final Collection<ARGNode<S, A>> nodes;
	private final Collection<ARGEdge<S, A>> edges;

	private final Collection<ARGNode<S, A>> initNodes;
	private final Collection<ARGNode<S, A>> targetNodes;

	private int nextId = 0;

	ARG(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
		nodes = new LinkedHashSet<>();
		edges = new HashSet<>();
		initNodes = new HashSet<>();
		targetNodes = new HashSet<>();
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

	public Collection<Counterexample<S, A>> getCounterexamples() {
		final List<Counterexample<S, A>> counterexamples = new ArrayList<>();

		for (final ARGNode<S, A> targetNode : getTargetNodes()) {
			final List<S> states = new ArrayList<>();
			final List<A> actions = new ArrayList<>();
			ARGNode<S, A> running = targetNode;
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

			counterexamples.add(new CounterexampleImpl<S, A>(states, actions));
		}

		assert counterexamples.size() == getTargetNodes().size();
		return counterexamples;
	}

	////

	public void close(final ARGNode<S, A> node) {
		for (final ARGNode<S, A> nodeToCoverWith : nodes) {
			if (nodeToCoverWith.getId() >= node.getId()) {
				break;
			}
			cover(node, nodeToCoverWith);
		}
	}

	private void cover(final ARGNode<S, A> nodeToCover, final ARGNode<S, A> nodeToCoverWith) {
		checkNotNull(nodeToCover);
		checkNotNull(nodeToCoverWith);
		checkArgument(nodes.contains(nodeToCover));
		checkArgument(nodes.contains(nodeToCoverWith));

		if (nodeToCover.isCovered() || nodeToCoverWith.existsAncestor(n -> nodeToCover.equals(n))) {
			return;
		}

		if (domain.isLeq(nodeToCover.getState(), nodeToCoverWith.getState())) {
			addCoveringEdge(nodeToCover, nodeToCoverWith);
			nodeToCover.foreachDescendants(ARGNode::clearCoveredNodes);
		}
	}

	////

	ARGNode<S, A> createInitNode(final S initState, final boolean target) {
		final ARGNode<S, A> initNode = createNode(initState, target);
		initNodes.add(initNode);
		return initNode;
	}

	ARGNode<S, A> createSuccNode(final ARGNode<S, A> node, final A action, final S succState, final boolean target) {
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
