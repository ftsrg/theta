package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class BlockCFGTransformer {

	public static CFG createBlocks(CFG input)
	{
		CFG output = input.copy();

		Set<CFGNode> marks = new HashSet<>();
		marks.add(output.getEntry());
		marks.add(output.getExit());

		GraphAlgorithm.DFS(output.getEntry(), s -> {
			/*
			 * Mark the nodes as we traverse the tree. A node needs to be marked if:
			 * 	1. The node is the entry or exit node.
			 * 	2. The node has a branch parent.
			 * 	3. The node is a branch node and it has multiple parents (it MAY be a loop node).
			 */
			if (s.getParents().size() > 1) {
				marks.add(s);
			}

			if (s.getChildren().size() > 1) {
				// This is a branch node
				for (CFGNode child : s.getChildren()) {
					marks.add(child);
				}
			}

			return false; // Do not stop the search
		});

		Map<CFGNode, List<CFGNode>> blockReplace = new HashMap<>();
		for (CFGNode node : marks) {
			/*
			 * All nodes between the marked nodes are sequential and can be merged into a basic block.
			 *
			 * Because the nodes are sequential, a simple DFS algorithm until the next mark
			 * will show all nodes on the path (in order).
			 */
			List<CFGNode> visited = GraphAlgorithm.DFS(node, s -> s != node && marks.contains(s));
			blockReplace.put(node, visited);
		}

		blockReplace.forEach((CFGNode old, List<CFGNode> visited) -> {

			List<StmtCFGNode> nodes = new ArrayList<>();

			visited.stream().filter(s -> s instanceof StmtCFGNode).forEach(s -> {
				nodes.add((StmtCFGNode) s);
			});

			if (nodes.isEmpty()) {
				return;
			}

			StmtCFGNode head = nodes.get(0);
			StmtCFGNode tail = nodes.get(nodes.size() - 1);
			BlockCFGNode block;
			if (tail instanceof BranchStmtCFGNode) {
				block = new BranchingBlockCFGNode(nodes);
			} else {
				block = new BlockCFGNode(nodes);
			}

			//for (CFGNode parent : head.getParents()) {
			//	int idx = parent.children.lastIndexOf(head);
			//	parent.children.set(idx, block);
			//}

			head.parentsReplace(block);
			tail.childrenReplace(block);
		});

		return output;
	}

	public static CFG splitBlocks(CFG input) {

		CFG output = input.copy();

		output.nodes().stream().filter(s -> s instanceof BlockCFGNode).forEach(node -> {
			BlockCFGNode block = (BlockCFGNode) node;
			List<StmtCFGNode> blockNodes = block.getContainedNodes();

			StmtCFGNode head = blockNodes.get(0);
			StmtCFGNode tail = blockNodes.get(blockNodes.size() - 1);

			node.parentsReplace(head);
			node.childrenReplace(tail);
		});

		return output;
	}


}
