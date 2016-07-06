package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;
import hu.bme.mit.inf.ttmc.slicer.graph.ReversibleGraphNode;

public class PDGNode implements ReversibleGraphNode {

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

	public void addFlowChild(PDGNode node)
	{
		this.flowChildren.add(node);
		node.flowParents.add(this);
	}

	public void addFlowParent(PDGNode node)
	{
		this.flowParents.add(node);
		node.flowChildren.add(this);
	}

	public Collection<PDGNode> getControlParents()
	{
		return this.controlParents;
	}

	public Collection<PDGNode> getControlChildren()
	{
		return this.controlChildren;
	}

	public Collection<PDGNode> getFlowParents()
	{
		return this.flowParents;
	}

	public Collection<PDGNode> getFlowChildren()
	{
		return this.flowChildren;
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
		Set<PDGNode> allChildren = new HashSet<>();

		allChildren.addAll(this.flowChildren);
		allChildren.addAll(this.controlChildren);

		return allChildren;
	}

	@Override
	public Collection<? extends ReversibleGraphNode> getParents() {
		Set<PDGNode> allParents = new HashSet<>();

		allParents.addAll(this.flowParents);
		allParents.addAll(this.controlParents);

		return allParents;
	}

	@Override
	public String getLabel() {
		return cfg.toString();
	}



}