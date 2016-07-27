package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public abstract class BasicBlock {

	protected final String name;
	protected final List<NonTerminatorIrNode> nodes;
	protected final List<BasicBlock> parents = new ArrayList<>();

	protected Function function;

	/**
	 * Constructs a new Basic Block with a given name and node list
	 *
	 * @param name	A label referring to this block
	 * @param nodes	A list of non-terminating instruction nodes
	 */
	public BasicBlock(String name, List<NonTerminatorIrNode> nodes) {
		this.name = name;
		this.nodes = nodes;
	}

	/**
	 * Get all children of this block
	 *
	 * @return An unmodifiable collection of this node's children
	 */
	public abstract Collection<? extends BasicBlock> children();

	/**
	 * Gets this block's terminator node
	 *
	 * @return A terminating node
	 */
	public abstract TerminatorIrNode getTerminator();

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

	public void setFunction(Function function) {
		this.function = function;
	}

	public List<NonTerminatorIrNode> getNodes() {
		return Collections.unmodifiableList(this.nodes);
	}

	public void addParent(BasicBlock block) {
		if (!this.parents.contains(block)) {
			this.parents.add(block);
		}
	}

	public String getLabel() {
		StringBuilder sb = new StringBuilder();
		this.nodes.forEach(s -> sb.append("   " + s.getLabel() + "\\n"));
		sb.append(this.getTerminator().getLabel() + "\\n");

		return sb.toString();
	}


}
