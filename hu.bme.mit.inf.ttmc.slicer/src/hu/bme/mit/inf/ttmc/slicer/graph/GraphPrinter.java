package hu.bme.mit.inf.ttmc.slicer.graph;

import java.util.HashMap;
import java.util.Map;

public class GraphPrinter {

	private static int uniqid = 0;

	public static String toGraphvizString(Graph graph)
	{
		StringBuilder sb = new StringBuilder();

		GraphNode entry = graph.getEntry();

		sb.append("digraph G {\n");
		processNode(entry, new HashMap<GraphNode, Integer>(), sb);
		sb.append("}\n");

		return sb.toString();
	}

	private static void processNode(GraphNode node, Map<GraphNode, Integer> visited, StringBuilder sb)
	{
		int id = ++uniqid;

		visited.put(node, id);
		sb.append(String.format("node_%d [label=\"%s\"];\n", id, node.getLabel()));
		for (GraphNode child : node.getChildren()) {
			if (!visited.containsKey(child)) {
				processNode(child, visited, sb);
			}
			sb.append(String.format("node_%d -> node_%d\n", id, visited.get(child)));
		}
	}


}
