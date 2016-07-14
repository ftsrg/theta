package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;


public class CFGPrinter {

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

			if (node instanceof BranchStmtCFGNode) {
				if (child == ((BranchStmtCFGNode)node).getThenNode()) {
					sb.append(String.format("node_%d -> node_%d [label=\" True\"]\n", id, visited.get(child)));
				} else {
					sb.append(String.format("node_%d -> node_%d [label=\"  False\"]\n", id, visited.get(child)));
				}
			} else if (node instanceof BranchingBlockCFGNode) {
				if (child == ((BranchingBlockCFGNode)node).getThenNode()) {
					sb.append(String.format("node_%d -> node_%d [label=\" True\"]\n", id, visited.get(child)));
				} else {
					sb.append(String.format("node_%d -> node_%d [label=\"  False\"]\n", id, visited.get(child)));
				}

			} else {
				sb.append(String.format("node_%d -> node_%d\n", id, visited.get(child)));
			}
		}
	}

}
