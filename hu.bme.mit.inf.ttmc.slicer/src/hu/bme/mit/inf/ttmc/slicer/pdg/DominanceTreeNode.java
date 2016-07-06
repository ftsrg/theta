package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class DominanceTreeNode implements GraphNode {

	private CFGNode cfg;
	private Collection<DominanceTreeNode> children = new HashSet<>();
	private DominanceTreeNode parent;

	public DominanceTreeNode(CFGNode cfg, DominanceTreeNode parent) {
		this.cfg = cfg;
		this.parent = parent;
	}

	public DominanceTreeNode getParent()
	{
		return this.parent;
	}

	public void addChild(DominanceTreeNode node) {
		this.children.add(node);
	}

	@Override
	public Collection<DominanceTreeNode> getChildren() {
		return this.children;
	}

	@Override
	public String getLabel() {
		return this.cfg.getLabel();
	}

	public CFGNode getCFGNode() {
		return this.cfg;
	}

}
