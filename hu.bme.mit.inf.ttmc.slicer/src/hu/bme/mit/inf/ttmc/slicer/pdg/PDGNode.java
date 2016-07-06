package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.Collection;
import java.util.HashSet;
import java.util.stream.Stream;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class PDGNode implements GraphNode {

	private Collection<PDGNode> controlParents = new HashSet<PDGNode>();
	private Collection<PDGNode> controlChildren = new HashSet<PDGNode>();

	private Collection<PDGNode> flowParents = new HashSet<PDGNode>();
	private Collection<PDGNode> flowChildren = new HashSet<PDGNode>();

	private CFGNode cfg;

	public PDGNode(CFGNode cfg) {
		this.cfg = cfg;
	}

	public void addControlChild(PDGNode node)
	{
		this.controlChildren.add(node);
		node.controlParents.add(this);
	}

	public void addControlParent(PDGNode node)
	{
		this.controlParents.add(node);
		node.controlChildren.add(this);
	}

	public Collection<PDGNode> getControlParents()
	{
		return this.controlParents;
	}

	public Collection<PDGNode> getControlChildren()
	{
		return this.controlChildren;
	}

	@Override
	public String toString() {
		return cfg.toString();
	}

	public CFGNode getCfg() {
		return cfg;
	}

	@Override
	public Collection<? extends GraphNode> getChildren() {
		return this.controlChildren;
	}

	@Override
	public String getLabel() {
		return cfg.toString();
	}



}