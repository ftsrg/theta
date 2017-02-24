package hu.bme.mit.theta.frontend.c.dependency;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.utils.BasicBlockUtils;

public class LoopAnalysis {

	public static class LoopAnalysisInfo {
		public final BasicBlock head;
		public final Set<BasicBlock> body = new LinkedHashSet<>();

		public LoopAnalysisInfo(final BasicBlock head) {
			this.head = head;
		}
	}

	/**
	 * Tells whether the given block is a loop header
	 *
	 * @param block
	 *            The block to check
	 * @param pdt
	 *            The post dominator tree of the CFG
	 *
	 * @return
	 */
	public static boolean isLoopHeader(final BasicBlock block, final DominatorTree dt) {
		// To determine whether a node is a loop header we need to find a back
		// edge.
		// The edge A -> B is a back edge, if B idom A.
		for (final BasicBlock parent : block.parents()) {
			if (dt.immediatelyDominates(block, parent)) {
				return true;
			}
		}

		return false;
	}

	public static List<LoopAnalysisInfo> findLoops(final Function function) {
		final DominatorTree dt = DominatorTree.createDominatorTree(function);
		final List<BasicBlock> blocks = function.getBlocksDFS();
		final List<LoopAnalysisInfo> result = new ArrayList<>();

		for (final BasicBlock block : blocks) {
			final List<BasicBlock> backEdges = new ArrayList<>();
			for (final BasicBlock parent : block.parents()) {
				if (dt.dominates(block, parent)) {
					backEdges.add(parent);
				}
			}

			if (!backEdges.isEmpty()) {
				final LoopAnalysisInfo info = new LoopAnalysisInfo(block);
				for (final BasicBlock tail : backEdges) {
					info.body.addAll(findLoopBody(tail, block));
				}
				result.add(info);
			}
		}

		return result;
	}

	private static List<BasicBlock> findLoopBody(final BasicBlock header, final BasicBlock tail) {
		return BasicBlockUtils.reverseDFS(header, tail);
	}

}
