package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class CFGPrinter {

	private static int uniqid = 0;


	public static String toGraphvizString(CFG graph)
	{
		return toGraphvizString(graph, false);
	}

	public static String toGraphvizString(CFG graph, boolean reverse)
	{
		StringBuilder sb = new StringBuilder();

		CFGNode entry = reverse ? graph.getExit() : graph.getEntry();

		sb.append("digraph G {\n");
		processNode(entry, new HashMap<CFGNode, Integer>(), sb, reverse);
		sb.append("}\n");

		return sb.toString();
	}

	private static void processNode(CFGNode node, Map<CFGNode, Integer> visited, StringBuilder sb, boolean reverse)
	{
		int id = ++uniqid;

		visited.put(node, id);
		sb.append(String.format("node_%d [label=\"%s\"];\n", id, node.getLabel()));

		List<CFGNode> children = reverse ? node.getParents() : node.getChildren();

		for (CFGNode child : children) {
			if (!visited.containsKey(child)) {
				processNode(child, visited, sb, reverse);
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
