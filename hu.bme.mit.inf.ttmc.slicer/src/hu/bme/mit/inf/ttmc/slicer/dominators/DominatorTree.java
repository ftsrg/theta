package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.Map;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

/**
 * A graph representing a dominator tree
 *
 * @author Gyula Sallai
 */
public class DominatorTree implements Graph {

	private DominatorTreeNode entry;
	private Map<CFGNode, DominatorTreeNode> mapping;

	/**
	 * Constructs a new dominator tree from a given entry node and CFGNode mapping
	 *
	 * @param entry The root of the dominator tree
	 * @param mapping A CFG -> DominatorTreeNode mapping
	 */
	public DominatorTree(DominatorTreeNode entry, Map<CFGNode, DominatorTreeNode> mapping) {
		this.entry = entry;
		this.mapping = mapping;
	}

	/**
	 * Return the corresponding DominatorTreeNode of a CFGNode
	 * @param node
	 * @return
	 */
	public DominatorTreeNode find(CFGNode node) {
		return this.mapping.get(node);
	}

	/**
	 * Tells whether if A immediately dominates B (whether A is the parent of B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a immediately dominates b, false otherwise
	 */
	public boolean immediatelyDominates(CFGNode a, CFGNode b) {
		return this.immediatelyDominates(this.find(a), this.find(b));
	}

	/**
	 * Tells whether if A immediately dominates B (whether A is the parent of B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a immediately dominates b, false otherwise
	 */
	public boolean immediatelyDominates(DominatorTreeNode a, DominatorTreeNode b) {
		return b.getParent() == a;
	}

	/**
	 * Tells whether if A dominates B
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a dominates b, false otherwise
	 */
	public boolean dominates(CFGNode a, CFGNode b) {
		return this.dominates(this.find(a), this.find(b));
	}

	/**
	 * Tells whether if A dominates B
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a dominates b, false otherwise
	 */
	public boolean dominates(DominatorTreeNode a, DominatorTreeNode b) {
		// A dominates B if A is the parent of B in the tree
		DominatorTreeNode parent = b.getParent();

		while (parent != null) {
			if (parent == a)
				return true;

			parent = parent.getParent();
		}

		return false;
	}

	/**
	 * Tells whether if A strictly dominates B (A dominates B and A != B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a strictly dominates b, false otherwise
	 */
	public boolean strictlyDominates(CFGNode a, CFGNode b) {
		return this.strictlyDominates(this.find(a), this.find(b));
	}

	/**
	 * Tells whether if A strictly dominates B (A dominates B and A != B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a strictly dominates b, false otherwise
	 */
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
