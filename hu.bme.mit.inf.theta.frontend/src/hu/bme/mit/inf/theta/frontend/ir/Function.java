package hu.bme.mit.inf.theta.frontend.ir;

import static hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory.Goto;
import static hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory.JumpIf;
import static hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory.Return;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Stack;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.common.Product3;
import hu.bme.mit.inf.theta.common.Tuple;
import hu.bme.mit.inf.theta.common.Tuple3;
import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode.BranchTableEntry;
import hu.bme.mit.inf.theta.frontend.ir.node.EntryNode;
import hu.bme.mit.inf.theta.frontend.ir.node.ExitNode;
import hu.bme.mit.inf.theta.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.theta.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.ReturnNode;
import hu.bme.mit.inf.theta.frontend.ir.node.TerminatorIrNode;

/**
 * Represents a function in the intermediate representation
 */
public class Function {


	private final String name;
	private final ProcDecl<? extends Type> proc;
	private final List<VarDecl<? extends Type>> locals = new ArrayList<>();
	//private final Map<String, BasicBlock> blocksMap = new HashMap<>();
	private final Map<ParamDecl<? extends Type>, VarDecl<? extends Type>> args = new HashMap<>();
	private final List<BasicBlock> blocks = new ArrayList<>();

	private BasicBlock entry;
	private BasicBlock exit;

	private EntryNode entryNode;
	private ExitNode exitNode;

	private static int copyId = 0;

	private GlobalContext context;

	public Function(String name, ProcDecl<? extends Type> proc) {
		this.name = name;
		this.proc = proc;

		this.exit = new BasicBlock(name + "_exit", this);
		this.exitNode = new ExitNode();

		this.exit.terminate(this.exitNode);
	}

	public Function copy(Map<BasicBlock, BasicBlock> newBlocks) {
		Function func = new Function(this.name, this.proc);
		for (BasicBlock block : this.blocks) {
			BasicBlock newBlock = func.createBlock(block.getName() + "_cpy" + copyId++);
			newBlocks.put(block, newBlock);
			for (NonTerminatorIrNode node : block.getNodes()) {
				newBlock.addNode(node.copy());
			}
		}

		// Terminate the blocks
		for (Entry<BasicBlock, BasicBlock> entry : newBlocks.entrySet()) {
			BasicBlock oldBlock = entry.getKey();
			BasicBlock newBlock = entry.getValue();

			TerminatorIrNode terminator = oldBlock.getTerminator();

			if (terminator instanceof GotoNode) {
				newBlock.terminate(Goto(newBlocks.get(((GotoNode) terminator).getTarget())));
			} else if (terminator instanceof JumpIfNode) {
				JumpIfNode jump = (JumpIfNode) terminator;
				newBlock.terminate(JumpIf(jump.getCondition(), newBlocks.get(jump.getThenTarget()), newBlocks.get(jump.getElseTarget())));
			} else if (terminator instanceof ReturnNode) {
				newBlock.terminate(Return(((ReturnNode) terminator).getExpr(), newBlocks.get(this.exit), newBlock));
			} else if (terminator instanceof ExitNode) {
				newBlock.terminate(new ExitNode());
			} else if (terminator instanceof EntryNode) {
				newBlock.terminate(new EntryNode(newBlocks.get(((EntryNode) this.entry.getTerminator()).getTarget())));
			} else if (terminator instanceof BranchTableNode) {
				BranchTableNode branchTable = new BranchTableNode(((BranchTableNode) terminator).getCondition());
				((BranchTableNode) terminator).getValueEntries().forEach(e -> {
					branchTable.addTarget(e.getValue(), newBlocks.get(e.getTarget()));
				});
				branchTable.setDefaultTarget(newBlocks.get(((BranchTableNode) terminator).getDefaultTarget()));

				newBlock.terminate(branchTable);
			} else {
				throw new UnsupportedOperationException("Invalid terminator node");
			}
		}

		func.setEntryBlock(newBlocks.get(this.entry));
		func.setExitBlock(newBlocks.get(this.exit));

		return func;
	}

	public BasicBlock copyBlock(BasicBlock block) {
		BasicBlock copy = this.createBlock(block.getName() + "_cpy" + this.copyId++);

		for (NonTerminatorIrNode node : block.getNodes()) {
			copy.addNode(node.copy());
		}

		return copy;
	}

	public Function copy() {
		return this.copy(new HashMap<>());
	}

	public void addParam(ParamDecl<? extends Type> param, VarDecl<? extends Type> local) {
		this.args.put(param, local);
	}

	public BasicBlock createBlock(String name) {
		BasicBlock bb = new BasicBlock(name, this);
		this.addBasicBlock(bb);

		return bb;
	}

	public void replaceBlock(BasicBlock oldBlock, BasicBlock newBlock, TerminatorIrNode terminator) {
		if (!oldBlock.isTerminated)
			throw new RuntimeException("The original block must be terminated.");

		if (newBlock.isTerminated)
			throw new RuntimeException("The substitue block must not be terminated.");

		// Remove references to the old block in children
		oldBlock.terminator.getTargets().forEach(t -> t.parents.remove(oldBlock));
		newBlock.terminate(terminator);

		this.blocks.remove(oldBlock);
		this.addBasicBlock(newBlock);

		if (this.entry == oldBlock)
			this.entry = newBlock;

		if (this.exit == oldBlock)
			this.exit = newBlock;
	}

	/**
	 * Performs a normalization pass on the function. Normalized function input is a common requirement for
	 * most transformations and should be called at the end of each transformation pass capable of changing the function structure.
	 *
	 * A normalized function has the following properties:
	 * <ul>
	 * 	<li> Does not contain blocks only containing a single goto terminator </li>
	 * 	<li> Does not contain unreachable blocks </li>
	 * 	<li> Does not contain single-child blocks which are the only parent of their child </li>
	 * 	<li> Does not contain unterminated blocks </li>
	 * </ul>
	 */
	public void normalize() {
		// Normalization attempt on a function with an unterminated block is an error
		if (this.blocks.stream().anyMatch(b -> !b.isTerminated)) {
			throw new RuntimeException("Cannot normalize function: There were unterminated blocks");
		}

		// Remove single 'goto' nodes
		List<BasicBlock> singleGotos = this.blocks
			.stream()
			.filter(block -> block.countNodes() == 0 && (block.getTerminator() instanceof GotoNode))
			.collect(Collectors.toList());

		for (BasicBlock block : singleGotos) {
			GotoNode terminator = (GotoNode) block.getTerminator();
			List<BasicBlock> parents = new ArrayList<>(block.parents());
			BasicBlock target = terminator.getTarget();

			for (BasicBlock parent : parents) {
				if (parent.getTerminator() instanceof GotoNode) {
					((GotoNode) parent.getTerminator()).setTarget(target);
				} else if (parent.getTerminator() instanceof JumpIfNode) {
					((JumpIfNode) parent.getTerminator()).replaceTarget(block, target);
				} else if (parent.getTerminator() instanceof BranchTableNode) {
					((BranchTableNode) parent.getTerminator()).replaceTarget(block, target);
				} else if (parent.getTerminator() instanceof EntryNode) {
					parent.getTerminator().replaceTarget(block, target);
				}
			}

			terminator.getTarget().removeParent(block);
		}

		this.removeUnreachableBlocks();
		this.mergeBlocks();
	}

	public void addLocalVariable(VarDecl<? extends Type> variable) {
		this.locals.add(variable);
	}

	public void addBasicBlock(BasicBlock block) {
		if (!this.blocks.contains(block))
			this.blocks.add(block);
	}

	public void removeBasicBlock(BasicBlock block) {
		if (block.isTerminated) {
			block.getTerminator().getTargets().forEach(t -> t.parents.remove(block));
		}

		this.blocks.remove(block);
	}

	public Collection<BasicBlock> getBlocks() {
		return this.blocks;
	}

	/**
	 * Returns this function's blocks in DFS order.
	 *
	 * The function should be normalized before calling this method.
	 *
	 * @return A list of basic blocks, in DFS traversal order
	 */
	public List<BasicBlock> getBlocksDFS() {
		Stack<BasicBlock> ws = new Stack<>();
		List<BasicBlock> visited = new ArrayList<>();
		ws.push(this.entry);

		while (!ws.isEmpty()) {
			BasicBlock bb = ws.pop();
			if (!visited.contains(bb)) {
				visited.add(bb);
				bb.children().forEach(s -> ws.push(s));
			}
		}

		return visited;
	}

	public String getName() {
		return this.name;
	}

	public void setEntryBlock(BasicBlock entry) {
		if (entry.getTerminator() instanceof EntryNode) {
			this.entry = entry;
			this.entryNode = (EntryNode) entry.getTerminator();
			this.addBasicBlock(entry);
		} else {
			throw new RuntimeException("Entry blocks should have an entry node terminator");
		}
	}

	public BasicBlock getEntryBlock() {
		return this.entry;
	}

	public EntryNode getEntryNode() {
		return this.entryNode;
	}

	public void setExitBlock(BasicBlock exit) {
		if (exit.getTerminator() instanceof ExitNode) {
			this.exit = exit;
			this.exitNode = (ExitNode) exit.getTerminator();
		} else {
			throw new RuntimeException("Exit blocks should have an exit node terminator");
		}
	}

	public BasicBlock getExitBlock() {
		return this.exit;
	}

	public ExitNode getExitNode() {
		return this.exitNode;
	}

	public Type getType() {
		return this.proc.getReturnType();
	}

	public GlobalContext getContext() {
		return context;
	}

	public void setContext(GlobalContext context) {
		this.context = context;
	}

	/**
	 * Perform a depth-first-search and remove blocks unreachable from the entry block.
	 */
	private void removeUnreachableBlocks() {
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

		// retain all visited and marked nodes
		List<BasicBlock> unreachable =  this.blocks
			.stream()
			.filter(b -> !visited.contains(b))
			.filter(b -> b != this.entry && b != this.exit)
			.collect(Collectors.toList());

		unreachable.forEach(b -> this.removeBasicBlock(b));
	}

	/**
	 * Merge single-child blocks into their child if they are their child's only parent
	 */
	private void mergeBlocks() {
		boolean change = true;
		while (change) {
			change = false;

			Optional<BasicBlock> result = this.blocks
				.stream()
				.filter(b -> {
					if (b.getTerminator() instanceof GotoNode) {
						GotoNode term = (GotoNode) b.getTerminator();
						if (term.getTarget() == this.exit)	// This child shouldn't be the exit node
							return false;

						// And this block should be the child's only parent
						return term.getTarget().parents.size() == 1;
					} else if (b.getTerminator() instanceof BranchTableNode) {
						BranchTableNode branch = (BranchTableNode) b.getTerminator();
						if (branch.getEntryCount() != 0) // The switch statement has only a default branch
							return false;

						return branch.getDefaultTarget().parents.size() == 1;
					}

					return false;
				})
				.findFirst();

			if (result.isPresent()) {
				BasicBlock block = result.get();
				BasicBlock child;
				if (block.getTerminator() instanceof GotoNode) {
					GotoNode terminator = (GotoNode) block.getTerminator();
					child = terminator.getTarget();
				} else if (block.getTerminator() instanceof BranchTableNode) {
					BranchTableNode terminator = (BranchTableNode) block.getTerminator();
					child = terminator.getDefaultTarget();
				} else {
					throw new AssertionError("Invalid terminator class");
				}

				TerminatorIrNode childTerm = child.getTerminator();
				// Remove this terminator and append the child block's nodes to this block
				block.clearTerminator();
				child.getNodes().forEach(n -> block.addNode(n));
				child.clearTerminator();
				block.terminate(childTerm);
				this.removeBasicBlock(child);

				change = true;
			}
		}
	}

	public Product3<BasicBlock, BasicBlock, BasicBlock> splitBlock(BasicBlock block, int idx) {
		BasicBlock before = this.createBlock("before_split_" + block.getName());
		BasicBlock split  = this.createBlock("split_" + block.getName());
		BasicBlock after  = this.createBlock("after_split_" + block.getName());

		// Add the nodes in the required range.
		block.getNodes().subList(0, idx).forEach(n -> before.addNode(n));
		split.addNode((NonTerminatorIrNode) block.getNodeByIndex(idx));
		block.getNodes().subList(idx + 1, block.getNodes().size()).forEach(n -> after.addNode(n));

		// Rewire parent terminators into the before block
		List<BasicBlock> parents = new ArrayList<>(block.parents());

		parents.forEach(p -> p.terminator.replaceTarget(block, before));

		before.terminate(Goto(split));
		split.terminate(Goto(after));

		// Rewire child targets
		TerminatorIrNode terminator = block.getTerminator();
		block.clearTerminator();

		after.terminate(terminator);

		// Clean up the old block
		block.clearNodes();
		this.blocks.remove(block);

		return Tuple.of(before, split, after);
	}

	public ProcDecl<? extends Type> getProcDecl() {
		return this.proc;
	}

	public VarDecl<? extends Type> getArgument(ParamDecl<?> param) {
		return this.args.get(param);
	}
}
