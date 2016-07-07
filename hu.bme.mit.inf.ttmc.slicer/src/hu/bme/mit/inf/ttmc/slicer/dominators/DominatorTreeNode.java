package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;
import hu.bme.mit.inf.ttmc.slicer.pdg.DominanceTreeNode;

public class DominatorTreeNode implements GraphNode {

	private CFGNode cfg;
	private Collection<DominatorTreeNode> children = new HashSet<>();
	private DominatorTreeNode parent;

	public DominatorTreeNode(CFGNode cfg) {
		this.cfg = cfg;
	}

	public DominatorTreeNode getParent() {
		return this.parent;
	}

	public void setParent(DominatorTreeNode node) {
		this.parent = node;
		this.parent.children.add(this);
	}

	@Override
	public Collection<DominatorTreeNode> getChildren() {
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
