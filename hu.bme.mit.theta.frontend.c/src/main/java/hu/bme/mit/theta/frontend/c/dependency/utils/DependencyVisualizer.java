package hu.bme.mit.theta.frontend.c.dependency.utils;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph.CallGraphNode;

public class DependencyVisualizer {

	private static final String CG_ID = "cg";
	private static final String CG_LABEL = "";
	
	public static Graph visualizeCallGraph(CallGraph cg) {
		Graph graph = new Graph(CG_ID, CG_LABEL);
		Map<CallGraphNode, String> ids = new HashMap<>();
		
		int cnt = 0;
		for (CallGraphNode node : cg.getNodes()) {
			String name = node.getProc().getName();
			String id = Integer.toString(cnt);
			
			graph.addNode(id, NodeAttributes.builder().label(name).build());
			
			ids.put(node, id);
			cnt++;
		}

		for (CallGraphNode node : cg.getNodes()) {
			for (CallGraphNode child : node.getTargetNodes()) {
				graph.addEdge(ids.get(node), ids.get(child), EdgeAttributes.builder().build());
			}
		}
		
		return graph;
	}
		
}
