package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.ConditionalTerminatorNode;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.GotoNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;
import hu.bme.mit.theta.frontend.c.ir.utils.IrPrinter;

public class ThinSlicer extends AbstractFunctionSlicer {

	@Override
	public Function slice(Function function, IrNode criteria) {
		// Build the dependency structures
		UseDefineChain ud = UseDefineChain.buildChain(function);
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		
		List<IrNode> dataDeps = new ArrayList<>();
		
		Queue<IrNode> wl = new ArrayDeque<>();
		wl.add(criteria);
		
		// Find the all nodes which the criteria transitively depends on
		// These nodes must be included in the slice as they define the values of the criteria variables
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!dataDeps.contains(current)) {
				dataDeps.add(current);
				ud.getDefinitions(current).forEach(node -> {
					wl.add(node);
				});
			}
		}
		
		//dataDeps.forEach(dep -> System.out.println(dep.toString()));
		
		// Find required control dependencies
		List<IrNode> controlDeps = new ArrayList<>();
		
		wl.addAll(dataDeps);
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!controlDeps.contains(current)) {
				if (!dataDeps.contains(current))
					controlDeps.add(current);
				
				cdg.getParentBlocks(current.getParentBlock()).stream().map(block -> block.getTerminator()).forEach(terminator -> {
					wl.add(terminator);
				});
			}			
		}

		//controlDeps.forEach(dep -> System.out.println(dep.toString()));
		
		List<IrNode> visited = new ArrayList<>();
		visited.addAll(controlDeps);
		visited.addAll(dataDeps);
		
		
		// Find required blocks
		Set<BasicBlock> visitedBlocks = visited.stream().map(n -> n.getParentBlock()).collect(Collectors.toSet());
		visitedBlocks.add(function.getExitBlock());

		// Build a queue for blocks needing removal
		List<BasicBlock> blocks = function.getBlocksDFS();
		Queue<BasicBlock> blocksToRemove = new ArrayDeque<>(blocks);
		blocksToRemove.removeAll(visitedBlocks);

		Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
		Function copy = function.copy(blockMap);
		
		int brId = 0;
		
		for (Entry<BasicBlock, BasicBlock> entry : blockMap.entrySet()) {
			BasicBlock oldBlock = entry.getKey();
			BasicBlock newBlock = entry.getValue();
			
			TerminatorIrNode terminator = oldBlock.getTerminator();
			if (controlDeps.contains(terminator)) {
				System.out.println("DING: " + terminator);
				
				// This is may be a branching node which need to be abstracted
				if (terminator instanceof JumpIfNode) {
					JumpIfNode branch = (JumpIfNode) newBlock.getTerminator();
					
					
					// Create a new temporary variable to represent a nondeterministic branch
					VarDecl<?> brTmp = Decls.Var("__br" + (brId++) + "__", Types.Int());
					Expr<? extends BoolType> brCond = Exprs.Neq(brTmp.getRef(), Exprs.Int(0));
					
					branch.setCondition(brCond);					
				}
			}
		}
		
		System.out.println(IrPrinter.toGraphvizString(copy));

		/*
		 * Find unneeded components.
		 *
		 * The basic idea is to find the largest connected subgraph in the CFG,
		 * whose nodes are in the set of unneeded blocks.
		 *
		 * The algorithm picks a block from the removal set and explores its
		 * parents and children. If a node has no unneeded parent, it is marked
		 * as a 'top' node, if it has no unneeded child, it is marked as a
		 * 'bottom' node.
		 *
		 * Edges into the top nodes need to be redirected into the common child
		 * of the bottom nodes, thus the unneeded subgraph can be eliminiated.
		 */
		while (!blocksToRemove.isEmpty()) {
			Set<BasicBlock> componentBlocks = new HashSet<>();

			BasicBlock start = blocksToRemove.poll();

			Queue<BasicBlock> blocksToVisit = new ArrayDeque<>();
			blocksToVisit.add(start);

			Set<BasicBlock> mergeBlocks = new HashSet<>();
			Map<BasicBlock, BasicBlock> topBlocks = new HashMap<>();

			while (!blocksToVisit.isEmpty()) {
				BasicBlock current = blocksToVisit.poll();

				// If a block has no unneeded parent, it is a top node
				for (BasicBlock parent : current.parents()) {
					if (visitedBlocks.contains(parent)) {
						topBlocks.put(parent, current);
					} else if (!componentBlocks.contains(parent)) {
						blocksToVisit.add(parent);
						blocksToRemove.remove(parent);
						componentBlocks.add(parent);
					}
				}

				// If a block has no unneeded child, it is a bottom node, and
				// its needed child is the merge node
				for (BasicBlock child : current.children()) {
					if (visitedBlocks.contains(child)) {
						mergeBlocks.add(child);
					} else if (!componentBlocks.contains(child)) {
						blocksToVisit.add(child);
						blocksToRemove.remove(child);
						componentBlocks.add(child);
					}
				}
			}

			if (mergeBlocks.size() != 1) {
				throw new AssertionError("This is a bug.");
			}

			BasicBlock merge = mergeBlocks.iterator().next();
			BasicBlock newMerge = blockMap.get(merge);

			topBlocks.forEach((block, target) -> {
				BasicBlock newBlock = blockMap.get(block);

				TerminatorIrNode terminator = newBlock.getTerminator();
				TerminatorIrNode newTerm = null;
				
				newBlock.clearTerminator();

				if (terminator instanceof GotoNode) {
					newTerm = NodeFactory.Goto(newMerge);
				} else if (terminator instanceof JumpIfNode) {
					JumpIfNode branch = (JumpIfNode) terminator;
					if (branch.getThenTarget() == target) {
						newTerm = NodeFactory.JumpIf(branch.getCondition(), newMerge,
								branch.getElseTarget());
					} else {
						newTerm = NodeFactory.JumpIf(branch.getCondition(), branch.getThenTarget(),	newMerge);
					}
				} else if (terminator instanceof EntryNode) {
					newTerm = new EntryNode(newMerge);
				} else if (terminator instanceof BranchTableNode) {
					BranchTableNode bt = (BranchTableNode) terminator;

					BranchTableNode newBt = new BranchTableNode(bt.getCondition());
					bt.getValueEntries().forEach(e -> {
						newBt.addTarget(e.getValue(), blockMap.get(e.getTarget()));
					});
					newBt.setDefaultTarget(blockMap.get(bt.getDefaultTarget()));

					if (bt.getDefaultTarget() != target) {
						Expr<? extends Type> value = bt.getValueFromTarget(target);
						BasicBlock newTarget = newBt.getTargetFromValue(value);

						newBt.replaceTarget(newTarget, newMerge);
					} else {
						newBt.setDefaultTarget(newMerge);
					}

					newTerm = newBt;
				} else {
					throw new AssertionError("Should not happen: " + terminator.getClass().getName());
				}

				newBlock.terminate(newTerm);
			});
		}

		// Remove unneeded instructions from needed blocks
		for (BasicBlock block : visitedBlocks) {
			BasicBlock newBlock = blockMap.get(block);
			for (int idx = block.countNodes() - 1; idx >= 0; idx--) {
				IrNode node = block.getNodeByIndex(idx);
				if (!visited.contains(node)) {
					newBlock.removeNode(idx);
				}
			}
		}

		// Perform a normalization pass to eliminate orphaned nodes
		copy.normalize();
		
		return copy;
	}

	@Override
	protected List<IrNode> markRequiredNodes(Function function, IrNode criteria) {
		throw new UnsupportedOperationException();
	}

}
