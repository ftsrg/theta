package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;
import hu.bme.mit.inf.ttmc.slicer.graph.ReversibleGraphNode;

public abstract class CFGNode implements ReversibleGraphNode {

	private Collection<CFGNode> parents = new HashSet<CFGNode>();
	private Collection<CFGNode> children = new HashSet<CFGNode>();

	abstract public CFGNode copy();

	public void addChild(CFGNode node) {
		this.children.add(node);
		node.parents.add(this);
	}

	public void addParent(CFGNode node) {
		this.parents.add(node);
		node.children.add(this);
	}

	public void removeParent(CFGNode node) {
		this.parents.remove(node);
		node.children.remove(this);
	}

	public void parentsReplace(CFGNode newNode)
	{
		for (CFGNode parent : this.parents) {
			parent.children.remove(this);
			newNode.addParent(parent);
		}
		this.parents.clear();
	}

	public void childrenReplace(CFGNode newNode)
	{
		for (CFGNode child : this.children) {
			child.parents.remove(this);
			newNode.addChild(child);
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

	public void remove()
	{
		for (CFGNode parent : this.parents) {
			parent.children.remove(this);
			parent.children.addAll(this.children);
		}

		for (CFGNode child : this.children) {
			child.parents.remove(this);
			child.parents.addAll(this.parents);
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
	public Collection<CFGNode> getChildren()
	{
		return this.children;
	}

	@Override
	public Collection<CFGNode> getParents()
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

}
