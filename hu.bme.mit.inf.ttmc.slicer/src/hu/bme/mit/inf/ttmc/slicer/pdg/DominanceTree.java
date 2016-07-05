package hu.bme.mit.inf.ttmc.slicer.pdg;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class DominanceTree implements Graph {

	private DominanceTreeNode entry;

	public DominanceTree(DominanceTreeNode entry)
	{
		this.entry = entry;
	}

	@Override
	public GraphNode getEntry() {
		return this.entry;
	}

	public static DominanceTree fromCFG(CFG cfg)
	{
		CFGNode cfgEntry = cfg.getEntry();
		Map<CFGNode, Set<CFGNode>> dominators = new HashMap<CFGNode, Set<CFGNode>>();

		Set<CFGNode> entryDoms = new HashSet<CFGNode>(cfg.nodes());
		entryDoms.remove(cfgEntry);

		dominators.put(cfgEntry, entryDoms);

		processCFGNode(cfg, cfgEntry, new HashSet<CFGNode>(), dominators);

		for (Entry<CFGNode, Set<CFGNode>> e : dominators.entrySet()) {
			System.out.println(e.getKey().getLabel());
			for (CFGNode d : e.getValue()) {
				System.out.println("   " + d.getLabel());
			}
		}


		DominanceTreeNode domEntry = new DominanceTreeNode(cfgEntry);
		processDominators(cfg, domEntry, dominators);

		return new DominanceTree(domEntry);
	}

	private static void processDominators(CFG cfg, DominanceTreeNode node, Map<CFGNode, Set<CFGNode>> dominators)
	{
		Set<CFGNode> dominated = dominators.get(node.getCFGNode());

		System.out.println(node.getLabel());
		for (CFGNode d : dominated) {
			boolean immediate = true;

			System.out.println("    " + d);
			// The node n is immediate dominator of d if:
			// 	(1) n dom d
			for (CFGNode c : cfg.nodes()) {
				// Find other dominators of d
				if (c == node.getCFGNode() || c == d)
					continue;

				if (dominates(c, d, dominators)) {
					System.out.println("        " + c);
					// If c is another dominator of d

					if (!dominates(c, node.getCFGNode(), dominators)) {
						// c must dominate n to be immediate dominator
						immediate = false;
						break;
					}
				}
			}

			if (immediate) {
				DominanceTreeNode newNode = new DominanceTreeNode(d);
				node.addChild(newNode);

				processDominators(cfg, newNode, dominators);
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
		for (CFGNode child : node.getChildren()) {
			if (!visited.contains(child)) {
				Set<CFGNode> reachable = new HashSet<CFGNode>();
				findReachableNodes(child, cfg.getEntry(), reachable);

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
		for (CFGNode child : entry.getChildren()) {
			if (!visited.contains(child) && child != node) {
				findReachableNodes(node, child, visited);
			}
		}
	}


}
