package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.node.ExitNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;

public class Function {

	private final String name;
	private final Type type;
	private final List<VarDecl<? extends Type>> locals = new ArrayList<>();
	private final Map<String, BasicBlock> blocks = new HashMap<>();

	private BasicBlock entry;
	private BasicBlock exit;

	public Function(String name, Type type) {
		this.name = name;
		this.type = type;

		this.exit = new BasicBlock(name + "_exit", this);
		this.exit.terminate(new ExitNode());
	}

	public BasicBlock createBlock(String name) {
		BasicBlock bb = new BasicBlock(name, this);
		this.addBasicBlock(bb);

		return bb;
	}

	public void normalize() {
		// Remove single 'goto' nodes
		List<BasicBlock> singleGotos = this.blocks.values()
			.stream()
			.filter(block -> block.countNodes() == 0 && (block.getTerminator() instanceof GotoNode))
			.collect(Collectors.toList());

		for (BasicBlock block : singleGotos) {
			GotoNode terminator = (GotoNode) block.getTerminator();
			List<BasicBlock> parents = new ArrayList<>(block.parents());

			for (BasicBlock parent : parents) {
				if (parent.getTerminator() instanceof GotoNode) {
					((GotoNode) parent.getTerminator()).setTarget(terminator.getTarget());
				} else if (parent.getTerminator() instanceof JumpIfNode) {
					((JumpIfNode) parent.getTerminator()).replaceTarget(block, terminator.getTarget());
				}
			}

			terminator.getTarget().removeParent(block);
		}

		this.removeUnreachableBlocks();
		//this.mergeBlocks();
	}

	public void removeUnreachableBlocks() {
		// Perform a DFS
		Stack<BasicBlock> stack = new Stack<>();
		List<BasicBlock> visited = new ArrayList<>();
		stack.push(this.entry);

		while (!stack.isEmpty()) {
			BasicBlock block = stack.pop();
			if (!visited.contains(block)) {
				visited.add(block);
				for (BasicBlock child : block.children()) {
					stack.push(child);
				}
			}
		}

		// retain all visited nodes
		this.blocks.values().retainAll(visited);
	}

	/**
	 * Merge single-child blocks into their child if they are their child's only parent
	 *
	 * TODO
	 */
	public void mergeBlocks() {
		List<BasicBlock> blocks = this.blocks.values()
			.stream()
			.filter(b -> {
				if (!(b.getTerminator() instanceof GotoNode)) // The node should have only one child
					return false;

				GotoNode term = (GotoNode) b.getTerminator();
				if (term.getTarget() == this.exit)	// This child shouldn't be the exit node
					return false;

				return term.getTarget().parents.size() == 1; // And this block should be the child's only parent
			})
			.collect(Collectors.toList());

		for (BasicBlock block : blocks) {
			GotoNode terminator = (GotoNode) block.getTerminator();
			List<NonTerminatorIrNode> nodes = new ArrayList<>();

			nodes.addAll(block.getNodes());
			nodes.addAll(terminator.getTarget().getNodes());
		}
	}

	public void addLocalVariable(VarDecl<? extends Type> variable) {
		this.locals.add(variable);
	}

	public void addBasicBlock(BasicBlock block) {
		this.blocks.put(block.getName(), block);
	}

	public Collection<BasicBlock> getBlocks() {
		return this.blocks.values();
	}

	public String getName() {
		return this.name;
	}

	public void setEntryBlock(BasicBlock entry) {
		this.entry = entry;
		this.addBasicBlock(entry);
	}

	public BasicBlock getEntryBlock() {
		return this.entry;
	}

	public void setExitBlock(BasicBlock exit) {
		this.exit = exit;
	}

	public BasicBlock getExitBlock() {
		return this.exit;
	}


}
