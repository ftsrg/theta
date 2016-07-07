package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.Map;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class DominatorTree implements Graph {

	private DominatorTreeNode entry;
	private Map<CFGNode, DominatorTreeNode> mapping;

	public DominatorTree(DominatorTreeNode entry, Map<CFGNode, DominatorTreeNode> mapping) {
		this.entry = entry;
		this.mapping = mapping;
	}

	public DominatorTreeNode find(CFGNode node)
	{
		return this.mapping.get(node);
	}

	public boolean dominates(DominatorTreeNode a, DominatorTreeNode b)
	{
		// A dominates B if A is the parent of B in the tree
		DominatorTreeNode parent = b.getParent();

		while (parent != null) {
			if (parent == a)
				return true;

			parent = parent.getParent();
		}

		return false;
	}

	public boolean strictlyDominates(DominatorTreeNode a, DominatorTreeNode b)
	{
		if (a == b)
			return false;

		return this.dominates(a, b);
	}

	@Override
	public GraphNode getEntry() {
		return this.entry;
	}

}
