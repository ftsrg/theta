package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class BasicBlock {

	protected final String name;
	protected final List<NonTerminatorIrNode> nodes;
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
		this.nodes = new ArrayList<>();
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
		this.nodes = nodes;
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
			throw new RuntimeException("Cannot terminate an already terminated block.");

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
	public Collection<? extends BasicBlock> parents() {
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
	 * Returns this block's node count
	 *
	 * @return The size of this block's instruction list
	 */
	public int countNodes() {
		return this.nodes.size();
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

//	@Override
//	public String toString() {
//		return this.getName();
//	}

	public void removeParent(BasicBlock parent) {
		this.parents.remove(parent);
	}


}
