package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class BasicBlockCFGTransformer {

	public static CFG buildBasicBlocks(CFG input)
	{
		CFGNode entry = input.getEntry().copy();
		CFGNode exit  = input.getExit().copy();

		Set<CFGNode> marks = new HashSet<>();

		marks.add(input.getEntry());
		marks.add(input.getExit());

		GraphAlgorithm.DFS(input.getEntry(), s -> {
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
			List<CFGNode> visited = GraphAlgorithm.DFS(node, s -> s != node && marks.contains(s));
			blockReplace.put(node, visited);
		}

		System.out.println(blockReplace);

		input.getExit().parentsReplace(exit);

		for (Entry<CFGNode, List<CFGNode>> e : blockReplace.entrySet()) {
			CFGNode oldNode = e.getKey();
			List<CFGNode> visited = e.getValue();

			List<Stmt> stmts = new ArrayList<>();
			for (CFGNode v : visited) {
				if (v instanceof StmtCFGNode) {
					stmts.add(((StmtCFGNode) v).getStmt());
				}
			}
			BasicBlockCFGNode block = new BasicBlockCFGNode(stmts);

			oldNode.parentsReplace(block);
			visited.get(visited.size() - 1).childrenReplace(block);
			if (oldNode == input.getEntry()) {
				entry.addChild(block);
			}
		}

		return new CFG(entry, exit);
	}

	public static CFG splitBasicBlocks(CFG input)
	{
		return input;
	}

}
