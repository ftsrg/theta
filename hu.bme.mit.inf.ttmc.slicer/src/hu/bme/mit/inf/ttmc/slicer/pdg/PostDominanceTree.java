package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class PostDominanceTree implements Graph {

	private DominanceTreeNode entry;
	private Map<CFGNode, DominanceTreeNode> cfgMapping = new HashMap<CFGNode, DominanceTreeNode>();

	public PostDominanceTree(DominanceTreeNode entry)
	{
		this.entry = entry;
	}

	@Override
	public GraphNode getEntry() {
		return this.entry;
	}

	public DominanceTreeNode findCFGNode(CFGNode node) {
		return this.cfgMapping.get(node);
	}

	public boolean dominates(DominanceTreeNode a, DominanceTreeNode b)
	{
		// A dominates B if A is the parent of B in the tree
		DominanceTreeNode parent = b.getParent();

		while (parent != null) {
			if (parent == a)
				return true;

			parent = parent.getParent();
		}

		return false;
	}

	public boolean strictlyDominates(DominanceTreeNode a, DominanceTreeNode b)
	{
		if (a == b)
			return false;

		return this.dominates(a, b);
	}

	public boolean dominates(CFGNode a, CFGNode b)
	{
		return this.dominates(this.findCFGNode(a), this.findCFGNode(b));
	}

	public static PostDominanceTree fromCFG(CFG cfg)
	{
		CFGNode cfgEntry = cfg.getExit();
		Map<CFGNode, Set<CFGNode>> dominators = new HashMap<CFGNode, Set<CFGNode>>();

		Set<CFGNode> entryDoms = new HashSet<CFGNode>(cfg.nodes());
		entryDoms.remove(cfgEntry);

		dominators.put(cfgEntry, entryDoms);

		processCFGNode(cfg, cfgEntry, new HashSet<CFGNode>(), dominators);

		DominanceTreeNode domEntry = new DominanceTreeNode(cfgEntry, null);
		Map<CFGNode, DominanceTreeNode> mapping = new HashMap<CFGNode, DominanceTreeNode>();
		mapping.put(cfgEntry, domEntry);

		/*
		for (Entry<CFGNode, Set<CFGNode>> e : dominators.entrySet()) {
			System.out.println(e.getKey());
			for (CFGNode v : e.getValue()) {
				System.out.println("    " + v);
			}
		}*/

		processDominators(cfg, domEntry, dominators, mapping);

		PostDominanceTree fdt = new PostDominanceTree(domEntry);
		fdt.cfgMapping = mapping;

		return fdt;
	}

	private static void processDominators(CFG cfg, DominanceTreeNode node, Map<CFGNode, Set<CFGNode>> dominators, Map<CFGNode, DominanceTreeNode> mapping)
	{
		Set<CFGNode> dominated = dominators.get(node.getCFGNode());

		for (CFGNode d : dominated) {
			boolean immediate = true;

			// The node n is immediate dominator of d if:
			// 	(1) n dom d
			for (CFGNode c : cfg.nodes()) {
				// Find other dominators of d
				if (c == node.getCFGNode() || c == d || c == cfg.getEntry())
					continue;

				if (dominates(c, d, dominators)) {
					// If c is another dominator of d

					if (!dominates(c, node.getCFGNode(), dominators)) {
						// c must dominate n to be immediate dominator
						immediate = false;
						break;
					}
				}
			}

			if (immediate) {
				DominanceTreeNode newNode = new DominanceTreeNode(d, node);
				mapping.put(d, newNode);
				node.addChild(newNode);

				processDominators(cfg, newNode, dominators, mapping);
			}
		}
	}

	private static boolean dominates(CFGNode dom, CFGNode node, Map<CFGNode, Set<CFGNode>> dominators)
	{
		return dominators.get(dom).contains(node);
	}

	private static void processCFGNode(CFG cfg, CFGNode node, Set<CFGNode> visited, Map<CFGNode, Set<CFGNode>> dominators)
	{
		// Def(Domination): Let G(V,E,r) be a graph with nodes V, edges E and a root node r.
		// The node v dominates u if all r --> u paths contains v. v dom u
		// The node v immediately dominates u if:
		//	v != u
		//	v dom u
		//  for any w != v such w dom u, we have w dom v
		//
		// Algorithm: Let S be all nodes reachable from r by paths avoiding v. The vertices D = V - {v} - S are those which are dominated by v.
		visited.add(node);

		for (CFGNode child : node.getParents()) {
			if (!visited.contains(child)) {
				Set<CFGNode> reachable = new HashSet<CFGNode>();
				findReachableNodes(child, cfg.getExit(), reachable);

				Set<CFGNode> dominated = new HashSet<CFGNode>(cfg.nodes());
				dominated.removeAll(reachable);
				dominated.remove(child);

				dominators.put(child, dominated);

				processCFGNode(cfg, child, visited, dominators);
			}
		}
	}

	private static void findReachableNodes(CFGNode node, CFGNode entry, Set<CFGNode> visited)
	{
		visited.add(entry);
		for (CFGNode child : entry.getParents()) {
			if (!visited.contains(child) && child != node) {
				findReachableNodes(node, child, visited);
			}
		}
	}
}
