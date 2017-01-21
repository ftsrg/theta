package hu.bme.mit.theta.frontend.c.ir.utils;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode.BranchTableEntry;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;

public class FunctionVisualizer {
	
	private static final String CFG_ID = "cfg";

	public static Graph visualize(Function cfg) {
		Graph graph = new Graph(CFG_ID, cfg.getName());
		Map<BasicBlock, String> ids = new HashMap<>();
		
		int cnt = 0;
		for (BasicBlock block : cfg.getBlocks()) {
			String id = Integer.toString(cnt);
			ids.put(block, id);
			
			graph.addNode(
				id,
				NodeAttributes.builder().label(block.getLabel()).build()
			);
			
			cnt++;
		}
		
		for (BasicBlock block : cfg.getBlocks()) {
			String nodeId = ids.get(block);
			
			if (block.getTerminator() instanceof JumpIfNode) {
				JumpIfNode terminator = (JumpIfNode) block.getTerminator();
				
				String then = ids.get(terminator.getThenTarget());
				String elze = ids.get(terminator.getElseTarget());
				
				graph.addEdge(nodeId, then, EdgeAttributes.builder().label("True").build());
				graph.addEdge(nodeId, elze, EdgeAttributes.builder().label("False").build());
			} else if (block.getTerminator() instanceof BranchTableNode) {
				BranchTableNode terminator = (BranchTableNode) block.getTerminator();
				for (BranchTableEntry entry : terminator.getValueEntries()) {
					graph.addEdge(
						nodeId,
						ids.get(entry.getTarget()),
						EdgeAttributes.builder().label(entry.getValue().toString()).build()
					);
				}
				
				BasicBlock defaultTarget = terminator.getDefaultTarget();
				graph.addEdge(nodeId, ids.get(defaultTarget), EdgeAttributes.builder().label("Default").build());
			} else {
				for (BasicBlock child : block.children()) {
					graph.addEdge(nodeId, ids.get(child), EdgeAttributes.builder().build());
				}
			}
		}
		
		return graph;
	}
	
}
