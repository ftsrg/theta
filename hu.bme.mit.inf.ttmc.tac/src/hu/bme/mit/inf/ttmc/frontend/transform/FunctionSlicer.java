package hu.bme.mit.inf.ttmc.frontend.transform;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.frontend.dependency.ControlDependencyGraph;
import hu.bme.mit.inf.ttmc.frontend.dependency.ProgramDependency;
import hu.bme.mit.inf.ttmc.frontend.dependency.ProgramDependency.PDGNode;
import hu.bme.mit.inf.ttmc.frontend.dependency.UseDefineChain;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.AssertNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.utils.IrPrinter;

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
					/*
					// Create a work copy of the function
					Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
					Function copy = function.copy(blockMap);

					// Find the old criteria node and get the new one
					BasicBlock newBlock = blockMap.get(block);
					int idx = block.getNodeIndex(node);
					IrNode newNode = newBlock.getNodeByIndex(idx);
					*/

					Function slice = this.slice(function, cdg, ud, node);

					result.add(slice);
				}
			}
		}

		return result;
	}

	public Function slice(Function function, ControlDependencyGraph cdg, UseDefineChain ud, IrNode criteria) {
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

		System.out.println(visited);
		Set<BasicBlock> visitedBlocks = visited.stream().map(n -> n.getParentBlock()).collect(Collectors.toSet());
		System.out.println(visitedBlocks);


		Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
		Function slice = new Function(function.getName(), function.getType());
		function.getBlocks().forEach(b -> blockMap.put(b, slice.createBlock(b.getName())));

		slice.setEntryBlock(blockMap.get(function.getEntryBlock()));
		slice.setExitBlock(blockMap.get(function.getExitBlock()));

		for (BasicBlock oldBlock : function.getBlocks()) {
			BasicBlock newBlock = blockMap.get(oldBlock);
			for (NonTerminatorIrNode node : oldBlock.getNodes()) {
				if (visited.contains(node)) {
					newBlock.addNode(node);
				}
			}

			// If the block points to a needed block, create the relationship, otherwise just point to the exit block
			TerminatorIrNode terminator = oldBlock.getTerminator();
			if (terminator instanceof JumpIfNode) {
				JumpIfNode jump = (JumpIfNode) terminator;
				BasicBlock then = jump.getThenTarget();
				BasicBlock elze = jump.getElseTarget();

				if (!visitedBlocks.contains(then)) {
					then = slice.getExitBlock();
				} else {
					then = blockMap.get(then);
				}

				if (!visitedBlocks.contains(elze)) {
					elze = slice.getExitBlock();
				} else {
					elze = blockMap.get(elze);
				}

				terminator = NodeFactory.JumpIf(jump.getCond(), then, elze);
			} else if (terminator instanceof GotoNode) {
				GotoNode gotoNode = (GotoNode) terminator;
				BasicBlock target = gotoNode.getTarget();

				if (!visitedBlocks.contains(target)) {
					target = slice.getExitBlock();
				} else {
					target = blockMap.get(target);
				}

				terminator = NodeFactory.Goto(target);
			}

			newBlock.terminate(terminator);
		}


/*
		Function slice = function.copy(blockMap);

		for (BasicBlock oldBlock : function.getBlocks()) {
			BasicBlock newBlock = blockMap.get(oldBlock);
			TerminatorIrNode terminator = oldBlock.getTerminator();
			List<NonTerminatorIrNode> nodes = new ArrayList<>(newBlock.getNodes()); // We need a copy, otherwise clearing the list would clear the reference too

			newBlock.clearTerminator();
			newBlock.clearNodes();

			// Remove unneeded nonterminals
			for (int i = 0; i < oldBlock.countNodes(); i++) {
				IrNode node = oldBlock.getNodeByIndex(i);
				if (visited.contains(node)) {
					newBlock.addNode(nodes.get(i));
				}
			}

			// Remove unneeded block targets
			if (terminator instanceof JumpIfNode) {
				JumpIfNode jump = (JumpIfNode) terminator;
				BasicBlock then = jump.getThenTarget();
				BasicBlock elze = jump.getElseTarget();

				if (!visitedBlocks.contains(then)) {
					then = slice.getExitBlock();
				} else {
					then = blockMap.get(then);
				}

				if (!visitedBlocks.contains(elze)) {
					elze = slice.getExitBlock();
				} else {
					elze = blockMap.get(elze);
				}

				terminator = NodeFactory.JumpIf(jump.getCond(), then, elze);
			} else if (terminator instanceof GotoNode) {
				GotoNode gotoNode = (GotoNode) terminator;
				BasicBlock target = gotoNode.getTarget();

				if (!visitedBlocks.contains(target)) {
					target = slice.getExitBlock();
				} else {
					target = blockMap.get(target);
				}

				terminator = NodeFactory.Goto(target);
			}

			newBlock.terminate(terminator);
		}
*/
		//slice.normalize();

		return slice;
	}

}
