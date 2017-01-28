package hu.bme.mit.theta.frontend.c.dependency.utils;

import java.awt.Color;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGEdge;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGEdgeType;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependenceGraph.PDGNode;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph.CallGraphNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;

public class DependencyVisualizer {

	private static final String CG_ID = "cg";
	private static final String CG_LABEL = "";
	
	private static final String PDG_ID = "pdg";
	private static final String PDG_LABEL = "";
	
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
	
	public static Graph visualizePDG(ProgramDependenceGraph pdg) {
		Graph graph = new Graph(PDG_ID, PDG_LABEL);
		
		Collection<PDGNode> nodes = pdg.getNodes();
		Collection<PDGEdge> edges = pdg.getEdges();
		
		Map<PDGNode, String> ids = new HashMap<>();
		
		int cnt = 0;
		for (PDGNode node : nodes) {
			String id = Integer.toString(cnt);
			String label = node.getNode().getLabel();
			
			graph.addNode(id, NodeAttributes.builder().label(label).build());
			
			ids.put(node, id);
			cnt++;
		}
		
		for (PDGEdge edge : edges) {
			String sourceId = ids.get(edge.getSource());
			String targetId = ids.get(edge.getTarget());
			Color color = edge.getType() == PDGEdgeType.CONTROL ? Color.BLUE : Color.GREEN;
			
			graph.addEdge(sourceId, targetId, EdgeAttributes.builder().color(color).build());
		}
		
		return graph;		
	}
}
