package hu.bme.mit.theta.frontend.c.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;

public class ProgramDependenceGraph {
	
	public static class PDGNode {
		private IrNode node;
		
		private PDGNode(IrNode node) {
			this.node = node;
		}
		
		public IrNode getNode() {
			return this.node;
		}
	}
	
	public static class PDGEdge {		
		private PDGNode source;
		private PDGNode target;

		PDGEdgeType type;
		
		private PDGEdge(PDGNode source, PDGNode target, PDGEdgeType type) {
			this.source = source;
			this.target = target;
			this.type = type;
		}
		
		public PDGNode getSource() {
			return this.source;
		}
		
		public PDGNode getTarget() {
			return this.target;
		}

		public PDGEdgeType getType() {
			return this.type;
		}
	}
	
	public enum PDGEdgeType {
		CONTROL, DATA
	}
	
	private final Map<IrNode, PDGNode> nodes;
	private final Collection<PDGEdge> edges;
	
	public ProgramDependenceGraph(Map<IrNode, PDGNode> nodes, Collection<PDGEdge> edges) {
		this.nodes = nodes;
		this.edges = edges;
	}
	
	public Collection<PDGNode> getNodes() {
		return this.nodes.values();
	}

	public Collection<PDGEdge> getEdges() {
		return this.edges;
	}
	
	
	public static ProgramDependenceGraph create(Function function) {
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		UseDefineChain ud = UseDefineChain.buildChain(function);	
		
		Map<IrNode, PDGNode> nodes = new HashMap<>();
		List<PDGEdge> edges = new ArrayList<>();
		
		// Construct the graph initially
		for (BasicBlock block : function.getBlocks()) {
			for (IrNode node : block.getAllNodes()) {
				nodes.put(node, new PDGNode(node));
			}
		}
		
		for (Entry<IrNode, PDGNode> entry : nodes.entrySet()) {
			IrNode node = entry.getKey();
			PDGNode pdg = entry.getValue();
			
			// Get all control dependencies of this edge
			List<BasicBlock> controlDeps = cdg.getParentBlocks(node.getParentBlock());
			List<NonTerminatorIrNode> flowDeps = ud.getDefinitions(node);
			
			for (BasicBlock block : controlDeps) {
				PDGNode terminator = nodes.get(block.getTerminator());
				edges.add(new PDGEdge(terminator, pdg, PDGEdgeType.CONTROL));
			}
			
			for (IrNode flowDep : flowDeps) {
				PDGNode def = nodes.get(flowDep);
				edges.add(new PDGEdge(def, pdg, PDGEdgeType.DATA));
			}
			
		}
		
		return new ProgramDependenceGraph(nodes, edges);		
	}

}
