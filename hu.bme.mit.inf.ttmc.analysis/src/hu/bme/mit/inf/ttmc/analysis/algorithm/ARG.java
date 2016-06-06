package hu.bme.mit.inf.ttmc.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;

public class ARG<S extends State, NodeLabel, EdgeLabel> {

	private final Domain<S> domain;

	private final Collection<ARGNode<S, NodeLabel, EdgeLabel>> nodes;
	private final Collection<ARGEdge<S, NodeLabel, EdgeLabel>> edges;

	private final Collection<ARGNode<S, NodeLabel, EdgeLabel>> initNodes;

	private int nextId = 0;

	ARG(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
		nodes = new LinkedHashSet<>();
		edges = new HashSet<>();
		initNodes = new HashSet<>();
	}

	////

	public Collection<ARGNode<S, NodeLabel, EdgeLabel>> getNodes() {
		return Collections.unmodifiableCollection(nodes);
	}

	public Collection<ARGEdge<S, NodeLabel, EdgeLabel>> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public Collection<ARGNode<S, NodeLabel, EdgeLabel>> getInitNodes() {
		return Collections.unmodifiableCollection(initNodes);
	}

	////

	public void close(final ARGNode<S, NodeLabel, EdgeLabel> node) {
		for (final ARGNode<S, NodeLabel, EdgeLabel> nodeToCoverWith : nodes) {
			if (nodeToCoverWith.getId() >= node.getId()) {
				break;
			}
			cover(node, nodeToCoverWith);
		}
	}

	private void cover(final ARGNode<S, NodeLabel, EdgeLabel> nodeToCover,
			final ARGNode<S, NodeLabel, EdgeLabel> nodeToCoverWith) {
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

	ARGNode<S, NodeLabel, EdgeLabel> createInitNode(final S initState, final boolean target) {
		final ARGNode<S, NodeLabel, EdgeLabel> initNode = createNode(initState, target);
		initNodes.add(initNode);
		return initNode;
	}

	ARGNode<S, NodeLabel, EdgeLabel> createSuccNode(final ARGNode<S, NodeLabel, EdgeLabel> node, final S succState,
			final boolean target) {
		checkArgument(nodes.contains(node));

		final ARGNode<S, NodeLabel, EdgeLabel> succNode = createNode(succState, target);
		createEdge(node, succNode);
		return succNode;
	}

	////

	private ARGEdge<S, NodeLabel, EdgeLabel> createEdge(final ARGNode<S, NodeLabel, EdgeLabel> source,
			final ARGNode<S, NodeLabel, EdgeLabel> target) {
		final ARGEdge<S, NodeLabel, EdgeLabel> edge = new ARGEdge<>(source, target);
		source.outEdges.add(edge);
		target.inEdge = Optional.of(edge);
		return edge;
	}

	private ARGNode<S, NodeLabel, EdgeLabel> createNode(final S state, final boolean target) {
		final ARGNode<S, NodeLabel, EdgeLabel> node = new ARGNode<>(state, nextId, target);
		nodes.add(node);
		nextId++;
		return node;
	}

	private void addCoveringEdge(final ARGNode<S, NodeLabel, EdgeLabel> nodeToCover,
			final ARGNode<S, NodeLabel, EdgeLabel> nodeToCoverWith) {
		nodeToCover.coveringNode = Optional.of(nodeToCoverWith);
		nodeToCoverWith.coveredNodes.add(nodeToCover);
	}

}
