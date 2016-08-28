package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class BasicBlock {

	protected final String name;
	protected final List<NonTerminatorIrNode> nodes = new ArrayList<>();
	protected final List<BasicBlock> parents = new ArrayList<>();

	protected Function function;
	protected boolean isTerminated = false;
	protected TerminatorIrNode terminator;

	/**
	 * Constructs a new BasicBlock with a given name and empty node list
	 *
	 * @param name
	 */
	public BasicBlock(String name, Function function) {
		this.name = name;
		this.function = function;
	}

	/**
	 * Constructs a new BasicBlock with a given name and node list
	 *
	 * @param name	A label referring to this block
	 * @param nodes	A list of non-terminating instruction nodes
	 */
	public BasicBlock(String name, Function function, List<NonTerminatorIrNode> nodes) {
		this.name = name;
		this.function = function;
		this.nodes.addAll(nodes);
	}

	/**
	 * Get all children of this block
	 *
	 * @return An unmodifiable collection of this node's children
	 */
	public List<BasicBlock> children() {
		return this.terminator.getTargets();
	}

	/**
	 * Gets this block's terminator node
	 *
	 * @return A terminating node
	 */
	public TerminatorIrNode getTerminator() {
		return this.terminator;
	}

	/**
	 * Terminates this block with a terminator node.
	 *
	 * @param node A terminator node
	 */
	public void terminate(TerminatorIrNode node) {
		if (this.isTerminated)
			throw new RuntimeException("Cannot terminate an already terminated block (" + this.name + ")");

		this.terminator = node;
		this.terminator.getTargets().forEach(s -> {
			s.addParent(this);
			this.function.addBasicBlock(s);
		});
		this.terminator.setParentBlock(this);

		this.isTerminated = true;
	}

	/**
	 * Appends a node to the node list
	 *
	 * @param node An instruction node
	 */
	public void addNode(NonTerminatorIrNode node) {
		if (this.isTerminated)
			throw new RuntimeException("Cannot append to a terminated block.");

		this.nodes.add(node);
		node.setParentBlock(this);
	}

	/**
	 * Tells whether this block terminated or not
	 *
	 * @return True if this block is terminated, false otherwise
	 */
	public boolean isTerminated() {
		return this.isTerminated;
	}

	/**
	 * Gets all parents of this block
	 *
	 * @return An unmodifiable collection of this node's parents
	 */
	public Collection<BasicBlock> parents() {
		return Collections.unmodifiableList(this.parents);
	}

	/**
	 * Returns this block's name
	 *
	 * @return The block label
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Returns the function containing this block
	 *
	 * @return A function object containing this block
	 */
	public Function getFunction() {
		return this.function;
	}

	/**
	 * Sets this node's function parent
	 *
	 * @param function A function object which should contain this block
	 */
	public void setFunction(Function function) {
		this.function = function;
	}

	/**
	 * Returns this block's contained nodes
	 *
	 * @return A collection of this block's instructions
	 */
	public List<NonTerminatorIrNode> getNodes() {
		return Collections.unmodifiableList(this.nodes);
	}

	/**
	 * Returns this block's nonterminator and terminator nodes
	 *
	 * @return A collcetion of all instructions of this block
	 */
	public List<IrNode> getAllNodes() {
		List<IrNode> allNodes = new ArrayList<>(this.nodes);
		allNodes.add(this.terminator);

		return Collections.unmodifiableList(allNodes);
	}

	/**
	 * Returns this block's node count
	 *
	 * @return The size of this block's instruction list
	 */
	public int countNodes() {
		return this.nodes.size();
	}

	/**
	 * Replace a node in this block with a new one
	 *
	 * @param oldNode The node to be replaced
	 * @param newNode The new node
	 */
	public void replaceNode(IrNode oldNode, IrNode newNode) {
		if (oldNode == this.terminator) {
			if (!(newNode instanceof TerminatorIrNode))
				throw new IllegalArgumentException("Cannot replace a terminator node with a nonterminator");

			TerminatorIrNode term = (TerminatorIrNode) newNode;
			if (!term.getTargets().equals(this.terminator.getTargets()))
				throw new IllegalArgumentException("Use clearTerminator and terminate to replace a terminator node with a terminator of different targets");

			this.terminator = term;
		} else if (newNode instanceof NonTerminatorIrNode) {
			int idx = this.nodes.indexOf(oldNode);
			if (idx == -1)
				throw new IllegalArgumentException("Old node was not found in the block");

			this.nodes.set(idx, (NonTerminatorIrNode) newNode);
		} else {
			System.out.println(this.terminator + " " + this.terminator.getLabel());
			System.out.println(oldNode + " " + oldNode.getLabel());
			System.out.println(newNode + " " + newNode.getLabel());
			throw new IllegalArgumentException("Cannot replace a nonterminator node with a terminator");
		}
	}

	/**
	 * Replace a node at a given index
	 *
	 * This method cannot replace terminator nodes
	 *
	 * @param idx	The index of the old node
	 * @param node	The new node
	 */
	public void replaceNode(int idx, NonTerminatorIrNode node) {
		if (idx >= this.nodes.size() || idx < 0)
			throw new IllegalArgumentException("Invalid node index");

		this.nodes.set(idx, node);
	}

	/**
	 * Returns a given node's index in the block
	 *
	 * This operation throws an exception if the node is not contained in the block
	 *
	 * @param node The node to search for
	 *
	 * @return The index of the given node
	 */
	public int getNodeIndex(IrNode node) {
		if (node == this.terminator)
			return this.nodes.size();

		int idx = this.nodes.indexOf(node);
		if (idx == -1)
			throw new IllegalArgumentException("The block does not contain the given node");

		return idx;
	}

	/**
	 * Returns the node on a given index
	 *
	 * This operation throws an exception if the node is not contained in the block
	 *
	 * @param idx	Index of the node to return
	 *
	 * @return The node on the specified position
	 */
	public IrNode getNodeByIndex(int idx) {
		if (idx == this.nodes.size())
			return this.terminator;

		return this.nodes.get(idx);
	}

	/**
	 * Remove a node by index
	 *
	 * @param idx The index of the node to remove
	 */
	public void removeNode(int idx) {
		if (idx < 0 || idx >= this.nodes.size())
			throw new IllegalArgumentException("The block '" + this.name + "' does not contain the given node index: " + idx);

		this.nodes.remove(idx);
	}

	/**
	 * Clear all nodes from this block
	 *
	 * If the block is already terminated, this operation fails with an exception.
	 * Use clearTerminator to reset the block terminator.
	 */
	public void clearNodes() {
		if (this.isTerminated)
			throw new RuntimeException("Cannot clear the node list of a terminated block");

		this.nodes.clear();
	}

	/**
	 * Clear the current terminator of this block
	 *
	 * If the block is not terminated, this operation fails with an exception.
	 */
	public void clearTerminator() {
		if (!this.isTerminated)
			throw new RuntimeException("Cannot clear the terminator of an unterminated block");

		this.terminator.getTargets().forEach(t -> t.removeParent(this));
		this.isTerminated = false;
	}

	/**
	 * Sets a block as a parent of this block
	 *
	 * @param block A block which has an edge into this block
	 */
	public void addParent(BasicBlock block) {
		if (!this.parents.contains(block)) {
			this.parents.add(block);
		}
	}

	/**
	 * Returns a string representation of this block's instructions
	 *
	 * @return A string containing the label of this node's instructions
	 */
	public String getLabel() {
		StringBuilder sb = new StringBuilder();
		this.nodes.forEach(s -> sb.append(s.getLabel() + "\\n"));

		sb.append(this.getTerminator().getLabel() + "\\n");

		return sb.toString();
	}

	@Override
	public String toString() {
		return this.getName();
	}

	public void removeParent(BasicBlock parent) {
		this.parents.remove(parent);
	}


}
