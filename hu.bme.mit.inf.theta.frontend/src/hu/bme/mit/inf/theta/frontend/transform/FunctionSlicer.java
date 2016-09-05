package hu.bme.mit.inf.theta.frontend.transform;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.frontend.dependency.ControlDependencyGraph;
import hu.bme.mit.inf.theta.frontend.dependency.UseDefineChain;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.node.AssertNode;
import hu.bme.mit.inf.theta.frontend.ir.node.EntryNode;
import hu.bme.mit.inf.theta.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory;
import hu.bme.mit.inf.theta.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.TerminatorIrNode;
import hu.bme.mit.inf.theta.frontend.ir.utils.IrPrinter;

public class FunctionSlicer {

	public static final Predicate<IrNode> SLICE_ON_ASSERTS = (IrNode s) -> s instanceof AssertNode;

	public List<Function> allSlices(Function function, Predicate<IrNode> pred) {
		List<Function> result = new ArrayList<>();
		List<BasicBlock> blocks = function.getBlocksDFS();

		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		UseDefineChain ud = UseDefineChain.buildChain(function);

		System.out.println(IrPrinter.controlDependencyGraph(cdg));

		// Find the predicate nodes
		for (BasicBlock block : blocks) {
			for (IrNode node : block.getAllNodes()) {
				if (pred.test(node)) {
					Function slice = this.slice(function, cdg, ud, node);
					result.add(slice);
				}
			}
		}

		return result;
	}

	public Function slice(Function function, ControlDependencyGraph cdg, UseDefineChain ud, IrNode criteria) {
		// Perform slicing
		List<IrNode> visited = findRequiredNodes(cdg, ud, criteria);

		// Find required blocks
		Set<BasicBlock> visitedBlocks = visited.stream()
			.map(n -> n.getParentBlock())
			.collect(Collectors.toSet());
		visitedBlocks.add(function.getExitBlock());

		// Build a queue for blocks needing removal
		List<BasicBlock> blocks = function.getBlocksDFS();
		Queue<BasicBlock> blocksToRemove = new ArrayDeque<>(blocks);
		blocksToRemove.removeAll(visitedBlocks);

		Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
		Function copy = function.copy(blockMap);

		/*
		 * Find unneeded components.
		 *
		 * The basic idea is to find the largest connected subgraph in the CFG, whose nodes are in the set of unneeded blocks.
		 *
		 * The algorithm picks a block from the removal set and explores its
		 * parents and children. If a node has no unneeded parent, it is marked as a 'top' node,
		 * if it has no unneeded child, it is marked as a 'bottom' node.
		 *
		 * Edges into the top nodes need to be redirected into the common child of the bottom nodes,
		 * thus the unneeded subgraph can be eliminiated.
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

				// If a block has no unneeded child, it is a bottom node, and its needed child is the merge node
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

			topBlocks.forEach((BasicBlock block, BasicBlock target) -> {
				BasicBlock newBlock = blockMap.get(block);
				newBlock.clearTerminator();

				TerminatorIrNode terminator = block.getTerminator();
				TerminatorIrNode newTerm = null;

				if (terminator instanceof GotoNode) {
					newTerm = NodeFactory.Goto(newMerge);
				} else if (terminator instanceof JumpIfNode) {
					JumpIfNode branch = (JumpIfNode) terminator;
					if (branch.getThenTarget() == target) {
						newTerm = NodeFactory.JumpIf(branch.getCond(), newMerge, blockMap.get(branch.getElseTarget()));
					} else {
						newTerm = NodeFactory.JumpIf(branch.getCond(), blockMap.get(branch.getThenTarget()), newMerge);
					}
				} else if (terminator instanceof EntryNode) {
					newTerm = new EntryNode(newMerge);
				} else {
					throw new AssertionError("Should not happen");
				}

				newBlock.terminate(newTerm);
			});
		}

		// Remove unneeded instructions from needed blocks
		for (BasicBlock block : visitedBlocks) {
			BasicBlock newBlock = blockMap.get(block);
			for (int idx = block.countNodes() - 1; idx >= 0; idx--) {
				IrNode node = block.getNodeByIndex(idx);
				if (!visited.contains(node))
					newBlock.removeNode(idx);
			}
		}

		// Perform a normalization pass to eliminate orphaned nodes
		copy.normalize();

		return copy;
	}

	private List<IrNode> findRequiredNodes(ControlDependencyGraph cdg, UseDefineChain ud, IrNode criteria) {
		Queue<IrNode> worklist = new ArrayDeque<IrNode>();
		List<IrNode> visited = new ArrayList<>();

		worklist.add(criteria);

		while (!worklist.isEmpty()) {
			IrNode current = worklist.poll();

			if (!visited.contains(current)) {
				visited.add(current);

				Collection<NonTerminatorIrNode> flowDeps = ud.getDefinitions(current).stream()
					.filter(d -> !visited.contains(d))
					.collect(Collectors.toList());

				Collection<TerminatorIrNode> controlDeps = cdg.getParentBlocks(current.getParentBlock()).stream()
					.map(b -> b.getTerminator())
					.filter(t -> !visited.contains(t))
					.collect(Collectors.toList());

				worklist.addAll(flowDeps);
				worklist.addAll(controlDeps);
			}
		}

		return visited;
	}

}
