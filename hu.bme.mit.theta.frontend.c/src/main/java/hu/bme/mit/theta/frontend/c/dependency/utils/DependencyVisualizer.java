package hu.bme.mit.theta.frontend.c.dependency.utils;

import java.awt.Color;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph.CallGraphNode;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGEdge;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGEdgeType;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGNode;

public class DependencyVisualizer {

	private static final String CG_ID = "cg";
	private static final String CG_LABEL = "";

	private static final String PDG_ID = "pdg";
	private static final String PDG_LABEL = "";

	public static Graph visualizeCallGraph(final CallGraph cg) {
		final Graph graph = new Graph(CG_ID, CG_LABEL);
		final Map<CallGraphNode, String> ids = new HashMap<>();

		int cnt = 0;
		for (final CallGraphNode node : cg.getNodes()) {
			final String name = node.getProc().getName();
			final String id = Integer.toString(cnt);

			graph.addNode(id, NodeAttributes.builder().label(name).build());

			ids.put(node, id);
			cnt++;
		}

		for (final CallGraphNode node : cg.getNodes()) {
			for (final CallGraphNode child : node.getTargetNodes()) {
				graph.addEdge(ids.get(node), ids.get(child), EdgeAttributes.builder().build());
			}
		}

		return graph;
	}

	public static Graph visualizePDG(final ProgramDependenceGraph pdg) {
		final Graph graph = new Graph(PDG_ID, PDG_LABEL);

		final Collection<PDGNode> nodes = pdg.getNodes();
		final Collection<PDGEdge> edges = pdg.getEdges();

		final Map<PDGNode, String> ids = new HashMap<>();

		int cnt = 0;
		for (final PDGNode node : nodes) {
			final String id = Integer.toString(cnt);
			final String label = node.getNode().getLabel();

			graph.addNode(id, NodeAttributes.builder().label(label).build());

			ids.put(node, id);
			cnt++;
		}

		for (final PDGEdge edge : edges) {
			final String sourceId = ids.get(edge.getSource());
			final String targetId = ids.get(edge.getTarget());
			final Color color = edge.getType() == PDGEdgeType.CONTROL ? Color.BLUE : Color.GREEN;

			graph.addEdge(sourceId, targetId, EdgeAttributes.builder().color(color).build());
		}

		return graph;
	}
}
