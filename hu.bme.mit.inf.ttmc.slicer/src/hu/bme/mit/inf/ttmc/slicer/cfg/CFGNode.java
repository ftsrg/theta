package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;
import hu.bme.mit.inf.ttmc.slicer.graph.ReversibleGraphNode;

public abstract class CFGNode implements ReversibleGraphNode {

	protected List<CFGNode> parents = new ArrayList<CFGNode>();
	protected List<CFGNode> children = new ArrayList<CFGNode>();

	abstract public CFGNode copy();

	public void addChild(CFGNode node) {
		if (this.children.contains(node))
			return;

		this.children.add(node);
		node.parents.add(this);
	}

	public void addParent(CFGNode node) {
		if (this.parents.contains(node))
			return;

		this.parents.add(node);
		node.children.add(this);
	}

	public void removeParent(CFGNode node) {
		this.parents.remove(node);
		node.children.remove(this);
	}

	public void removeChild(CFGNode node) {
		this.children.remove(node);
		node.parents.remove(this);
	}

	public void parentsReplace(CFGNode newNode)
	{
		for (CFGNode parent : this.parents) {
			int idx = parent.children.lastIndexOf(this);
			parent.children.set(idx, newNode);
			newNode.parents.add(parent);
		}
		this.parents.clear();
	}

	public void childrenReplace(CFGNode newNode)
	{
		for (CFGNode child : this.children) {
			int idx = child.parents.lastIndexOf(this);
			child.parents.set(idx, newNode);
			newNode.children.add(child);
		}

		this.children.clear();
	}

	public void clearParents()
	{
		this.parents.clear();
	}

	public void clearChildren()
	{
		this.children.clear();
	}

	public void replace(CFGNode newNode)
	{
		this.parentsReplace(newNode);
		this.childrenReplace(newNode);
	}

	public void parentsAddAll(Collection<? extends CFGNode> nodes) {
		for (CFGNode node : nodes) {
			if (this.parents.contains(node))
				continue;

			this.parents.add(node);
		}
	}

	public void childrenAddAll(Collection<? extends CFGNode> nodes) {
		for (CFGNode node : nodes) {
			if (this.children.contains(node))
				continue;

			this.children.add(node);
		}
	}

	public void remove()
	{
		for (CFGNode parent : this.parents) {
			parent.children.remove(this);
			parent.childrenAddAll(this.children);
		}

		for (CFGNode child : this.children) {
			child.parents.remove(this);
			child.parentsAddAll(this.parents);
		}
	}

	public Collection<CFGNode> successors()
	{
		return GraphAlgorithm.DFS(this);
	}

	public Collection<CFGNode> predecessors()
	{
		return GraphAlgorithm.reverseDFS(this);
	}

	@Override
	public List<CFGNode> getChildren()
	{
		return this.children;
	}

	@Override
	public List<CFGNode> getParents()
	{
		return this.parents;
	}

	public Set<CFGNode> getSuccessors() {
		Stack<CFGNode> stack = new Stack<CFGNode>();
		Set<CFGNode> visited = new HashSet<CFGNode>();

		stack.push(this);
		while (!stack.empty()) {
			CFGNode node = stack.pop();
			if (!visited.contains(node)) {
				visited.add(node);
				for (CFGNode child : node.getChildren()) {
					stack.push(child);
				}
			}
		}

		return visited;
	}

	public void removeChildren() {
		this.children.forEach(s -> s.parents.remove(this));
		this.clearChildren();
	}

}
