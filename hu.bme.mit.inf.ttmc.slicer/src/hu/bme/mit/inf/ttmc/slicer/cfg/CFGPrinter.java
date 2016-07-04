package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class CFGPrinter {

	private static class Edge
	{
		public CFGNode source;
		public CFGNode target;

		Edge(CFGNode source, CFGNode target) { this.source = source; this.target = target; }
	}


	private static int uniqid = 0;

	public static void countEdges(CFGNode cfg, Set<Edge> edges, Map<CFGNode, Integer> nodes)
	{
		for (CFGNode node : cfg.getChildren()) {
			edges.add(new Edge(cfg, node));
			if (!nodes.containsKey(node)) {
				nodes.put(node, uniqid++);
				countEdges(node, edges, nodes);
			}
		}
	}

	public static String toGraphvizString(CFG cfg)
	{
		StringBuilder sb = new StringBuilder();

		Set<Edge> edges = new HashSet<>();
		Map<CFGNode, Integer> nodes = new HashMap<>();

		CFGNode entry = cfg.getInit();

		nodes.put(entry, uniqid++);
		countEdges(entry, edges, nodes);

		sb.append("digraph G {");
		for (Entry<CFGNode, Integer> node : nodes.entrySet()) {
			sb.append(String.format("node_%d [label=\"%s\"];\n", node.getValue(), node.getKey()));
		}

		for (Edge e : edges) {
			sb.append(String.format("node_%d -> node_%d\n", nodes.get(e.source), nodes.get(e.target)));
		}
		sb.append("}");


		return sb.toString();
	}

}
