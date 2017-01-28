package hu.bme.mit.theta.frontend.c.transform.slicer.utils;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.GotoNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;

public class SliceCreator {
	
	private SliceCreator() {}

	public static Function constructSlice(Function function, List<IrNode> visited) throws AssertionError {
		Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
		Function copy = function.copy();
		
		return constructSlice(function, visited, blockMap, copy);
	}
	
	public static Function constructSlice(Function function, List<IrNode> visited, Map<BasicBlock, BasicBlock> blockMap,
			Function copy) throws AssertionError {
		// Find required blocks
		Set<BasicBlock> visitedBlocks = visited.stream().map(n -> n.getParentBlock()).collect(Collectors.toSet());
		visitedBlocks.add(function.getExitBlock());

		// Build a queue for blocks needing removal
		List<BasicBlock> blocks = function.getBlocksDFS();
		Queue<BasicBlock> blocksToRemove = new ArrayDeque<>(blocks);
		blocksToRemove.removeAll(visitedBlocks);
		
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
	
}
