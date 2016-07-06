package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class PDGPrinter {

	private static class Edge
	{
		public PDGNode source;
		public PDGNode target;

		Edge(PDGNode source, PDGNode target) { this.source = source; this.target = target; }
	}


	private static int uniqid = 0;

	public static void countEdges(PDGNode pdg, Set<Edge> edges, Map<PDGNode, Integer> nodes)
	{
		for (PDGNode node : pdg.getControlChildren()) {
			edges.add(new Edge(pdg, node));
			if (!nodes.containsKey(node)) {
				nodes.put(node, uniqid++);
				countEdges(node, edges, nodes);
			}
		}
	}

	public static String toGraphvizString(PDG pdg)
	{
		StringBuilder sb = new StringBuilder();

		Set<Edge> edges = new HashSet<>();
		Map<PDGNode, Integer> nodes = new HashMap<>();

		PDGNode entry = pdg.getEntry();

		nodes.put(entry, uniqid++);
		countEdges(entry, edges, nodes);

		sb.append("digraph G {");
		for (Entry<PDGNode, Integer> node : nodes.entrySet()) {
			sb.append(String.format("node_%d [label=\"%s\"];\n", node.getValue(), node.getKey()));
		}

		for (Edge e : edges) {
			sb.append(String.format("node_%d -> node_%d [color=blue]\n", nodes.get(e.source), nodes.get(e.target)));
		}

		for (PDGNode node : nodes.keySet()) {
			for (PDGNode inner : nodes.keySet()) {
				if (node == inner)
					continue;

				if (node.getFlowChildren().contains(inner)) {
					sb.append(String.format("node_%d -> node_%d [color=green]\n", nodes.get(node), nodes.get(inner)));
				}
			}
		}

		sb.append("}");


		return sb.toString();
	}

}
