package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.utils.BasicBlockUtils;

public class LoopAnalysis {

	public static class LoopInfo {
		public final BasicBlock head;
		public final Set<BasicBlock> body = new LinkedHashSet<>();

		public LoopInfo(BasicBlock head) {
			this.head = head;
		}
	}

	/**
	 * Tells whether the given block is a loop header
	 *
	 * @param block The block to check
	 * @param pdt 	The post dominator tree of the CFG
	 *
	 * @return
	 */
	public static boolean isLoopHeader(BasicBlock block, DominatorTree dt) {
		// To determine whether a node is a loop header we need to find a back edge.
		// The edge A -> B is a back edge, if B idom A.
		for (BasicBlock parent : block.parents()) {
			if (dt.immediatelyDominates(block, parent)) {
				return true;
			}
		}

		return false;
	}

	public static List<LoopInfo> findLoops(Function function) {
		DominatorTree dt = DominatorTree.createDominatorTree(function);
		List<BasicBlock> blocks = function.getBlocksDFS();
		List<LoopInfo> result = new ArrayList<>();

		for (BasicBlock block : blocks) {
			List<BasicBlock> backEdges = new ArrayList<>();
			for (BasicBlock parent : block.parents()) {
				if (dt.dominates(block, parent)) {
					backEdges.add(parent);
				}
			}

			if (!backEdges.isEmpty()) {
				LoopInfo info = new LoopInfo(block);
				for (BasicBlock tail : backEdges) {
					info.body.addAll(findLoopBody(tail, block));
				}
				result.add(info);
			}
		}

		return result;
	}

	private static List<BasicBlock> findLoopBody(BasicBlock header, BasicBlock tail) {
		return BasicBlockUtils.reverseDFS(header, tail);
	}



}
