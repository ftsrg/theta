package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class DominanceTreeNode implements GraphNode {

	private CFGNode cfg;
	private Collection<DominanceTreeNode> children = new HashSet<>();

	public DominanceTreeNode(CFGNode cfg) {
		this.cfg = cfg;
	}

	public void addChild(DominanceTreeNode node) {
		this.children.add(node);
	}

	@Override
	public Collection<? extends GraphNode> getChildren() {
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
