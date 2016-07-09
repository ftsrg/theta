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
			/*
			 * All nodes between the marked nodes are sequential and can be merged into a basic block.
			 *
			 * Because the nodes are sequential, a simple DFS algorithm until the next mark will show all nodes on the path (in order).
			 */
			List<CFGNode> visited = GraphAlgorithm.DFS(node, s -> s != node && marks.contains(s));
			blockReplace.put(node, visited);
		}

		// Set the new exit
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

			oldNode.parentsReplace(block); // The head of the block will have the first element's parents
			visited.get(visited.size() - 1).childrenReplace(block); // The tail of the block will have the last element's parents
			if (oldNode == input.getEntry()) {
				entry.addChild(block);
			}
		}

		return new CFG(entry, exit);
	}

	public static CFG splitBasicBlocks(CFG input)
	{
		CFG output = input.copy();

		for (CFGNode node : output.nodes()) {
			if (node instanceof BasicBlockCFGNode) {
				BasicBlockCFGNode block = (BasicBlockCFGNode) node;
				List<Stmt> stmts = block.getStmts();

				Stmt head = stmts.get(0);
				StmtCFGNode headNode = new StmtCFGNode(head);
				node.parentsReplace(headNode);

				List<Stmt> tail = stmts.subList(1, stmts.size());
				while (tail.size() != 0) {
					head = tail.get(0);
					StmtCFGNode localHeadNode = new StmtCFGNode(head);
					headNode.addChild(localHeadNode);
					headNode = localHeadNode;
					tail = tail.subList(1, tail.size());
				}
				node.childrenReplace(headNode);
			}
		}

		return output;
	}

}
