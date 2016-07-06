package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class PDG implements Graph {

	private PDGNode entry;

	public PDG(PDGNode entry)
	{
		this.entry = entry;
	}

	@Override
	public PDGNode getEntry() {
		return entry;
	}

	public static PDG fromCFG(CFG cfg)
	{
		PostDominanceTree pdt = PostDominanceTree.fromCFG(cfg);
		Set<CFGNode> nodes = cfg.nodes();

		Map<CFGNode, Set<CFGNode>> controlDeps = new HashMap<>();

		for (CFGNode node : nodes) {
			Set<CFGNode> dependants = new HashSet<CFGNode>();
			controlDeps.put(node, dependants);
			DominanceTreeNode A = pdt.findCFGNode(node);

			// Get all A -> B edges
			for (CFGNode child : node.getChildren()) {
				DominanceTreeNode B = pdt.findCFGNode(child);

				if (!pdt.dominates(B, A)) { // B must not postdominate A
					DominanceTreeNode parent = B;
					while (parent != A && parent != A.getParent()) {
						if (parent == null) break;
						dependants.add(parent.getCFGNode());
						parent = parent.getParent();
					}
				}
			}
		}

		Map<CFGNode, PDGNode> cdgMap = new HashMap<CFGNode, PDGNode>();
		for (CFGNode node : nodes) {
			PDGNode pdgNode = new PDGNode(node);
			cdgMap.put(node, pdgNode);
		}

		for (CFGNode node : nodes) {
			PDGNode pdgNode = cdgMap.get(node);
			for (CFGNode dependant : controlDeps.get(node)) {
				pdgNode.addControlChild(cdgMap.get(dependant));
			}
		}

		PDGNode pdgEntry = cdgMap.get(cfg.getEntry());
		for (PDGNode pdgNode : cdgMap.values()) {
			if (pdgNode == pdgEntry)
				continue;

			if (pdgNode.getControlParents().isEmpty()) {
				pdgNode.addControlParent(pdgEntry);
			}
		}


		for (Entry<CFGNode, Set<CFGNode>> e : controlDeps.entrySet()) {
			System.out.println(e.getKey() + " " + e.getValue());
		}

		return new PDG(pdgEntry);

	}


}
