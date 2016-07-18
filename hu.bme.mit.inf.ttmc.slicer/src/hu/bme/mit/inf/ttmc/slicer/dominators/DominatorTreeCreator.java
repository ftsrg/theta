package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;

public class DominatorTreeCreator {

	private static class NodeInfo
	{
		public int dfs = 0;
		public int parent = 0;
		public int sdom = 0;
		public int idom = 0;
		public CFGNode node;
		public DominatorTreeNode domNode;

		public NodeInfo(CFGNode node) {
			this.node = node;
			this.domNode = new DominatorTreeNode(node);
		}

		@Override
		public String toString() {
			return dfs + " " + parent + " " + sdom;
		}
	}

	public static DominatorTree postDominatorTree(CFG cfg)
	{
		return buildTree(cfg, true);
	}

	public static DominatorTree dominatorTree(CFG cfg)
	{
		return buildTree(cfg, false);
	}

	private static DominatorTree buildTree(CFG cfg, boolean reverse)
	{
		Map<CFGNode, Set<CFGNode>> dominators = new HashMap<>();

		CFGNode root = reverse ? cfg.getExit() : cfg.getEntry();
		dominators.put(root, new HashSet<CFGNode>() {{
			add(root);
		}});

		List<CFGNode> nodes = new ArrayList<CFGNode>(cfg.nodes());

		for (CFGNode node : nodes) {
			if (node == root)
				continue;
			dominators.put(node, new HashSet<CFGNode>(nodes));
		}

		nodes.remove(root);
		boolean change = true;
		while (change) {
			change = false;

			for (CFGNode node : nodes) {
				Set<CFGNode> nodeDoms = new HashSet<>();
				nodeDoms.add(node);

				Iterator<CFGNode> iter = reverse ? node.getChildren().iterator() : node.getParents().iterator();
				CFGNode first = iter.next();
				Set<CFGNode> parentDoms = new HashSet<>(dominators.get(first));
				//System.out.println("Node: " + node);
				//System.out.println("    " + first + ": " + parentDoms);
				while (iter.hasNext()) {
					CFGNode next = iter.next();
					parentDoms.retainAll(dominators.get(next));
					//System.out.println("    " + next + ": " + parentDoms);
				}

				nodeDoms.addAll(parentDoms);

				if (!dominators.get(node).equals(nodeDoms)) {
					dominators.put(node, nodeDoms);
					change = true;
				}
			}
		}

		// Find immediate dominators
		// p is immediate dominator of q (p idom q), if:
		//	1. p dom q
		//	2. every other dominator of q dominates p

		Map<CFGNode, DominatorTreeNode> domMapping = new HashMap<>();
		for (CFGNode node : nodes) {
			domMapping.put(node, new DominatorTreeNode(node));
		}
		domMapping.put(root, new DominatorTreeNode(root));

		dominators.forEach((CFGNode node, Set<CFGNode> doms) -> {
			// Node: The node being checked
			// Doms: The dominators of this node

			for (CFGNode dominator : doms) {
				if (dominator == node)
					continue;

				boolean isIdom = true;

				// Is this node an immediate dominator?
				// 	It is immediate if all other dominators of this node dominate it.
				for (CFGNode otherDominator : doms) {
					if (otherDominator == node || otherDominator == dominator)
						continue;


					if (!dominators.get(dominator).contains(otherDominator)) {
						isIdom = false;
						break;
					}
				}

				if (isIdom) {
					domMapping.get(node).setParent(domMapping.get(dominator));
					break;
				}

			}

		});

		return new DominatorTree(domMapping.get(root), domMapping);
	}
}
