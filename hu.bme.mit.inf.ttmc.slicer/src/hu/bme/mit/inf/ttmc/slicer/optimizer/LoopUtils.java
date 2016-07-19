package hu.bme.mit.inf.ttmc.slicer.optimizer;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class LoopUtils {

	/**
	 * Tells whether the given CFG node is a loop header
	 *
	 * @param node The condition node to check
	 * @param pdt The post dominator tree of the CFG
	 *
	 * @return
	 */
	public static boolean isLoopHeader(BranchStmtCFGNode node, DominatorTree pdt) {
		// To determine whether a node is a loop header we need to find a back edge.
		// The edge A -> B is a back edge, if B ipdom A.
		for (CFGNode parent : node.getParents()) {
			if (pdt.dominates(node, parent)) {
				return true;
			}
		}

		return false;
	}

	/**
	 * Return the node which is at the tail of a given loop's back edge
	 *
	 * @param node
	 * @param pdt
	 *
	 * @return
	 */
	public static CFGNode getBackEdgeTail(BranchStmtCFGNode node, DominatorTree dt) {
		for (CFGNode parent : node.getParents()) {
			if (dt.dominates(node, parent)) {
				return parent;
			}
		}

		throw new IllegalArgumentException("The given node is not a loop since it has no back edge.");
	}

	public static List<CFGNode> getLoopBody(BranchStmtCFGNode node, CFGNode tail) {
		List<CFGNode> nodes = GraphAlgorithm.reverseDFS(tail, s -> {
			return s == node;
		});
		nodes.add(node);

		return nodes;
	}


	public static List<BranchStmtCFGNode> findLoopHeaders(CFG cfg, DominatorTree dt) {
		List<BranchStmtCFGNode> loops = cfg.nodes().stream()
			.filter(s -> s instanceof BranchStmtCFGNode)
			.map(s -> (BranchStmtCFGNode) s)
			.filter(s -> LoopUtils.isLoopHeader(s, dt))
			.collect(Collectors.toList());

		return loops;
	}


}
