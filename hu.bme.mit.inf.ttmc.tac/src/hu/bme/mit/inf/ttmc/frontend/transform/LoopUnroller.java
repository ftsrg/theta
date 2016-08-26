package hu.bme.mit.inf.ttmc.frontend.transform;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.frontend.dependency.LoopAnalysis;
import hu.bme.mit.inf.ttmc.frontend.dependency.LoopAnalysis.LoopInfo;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class LoopUnroller implements FunctionTransformer {

	private int depth;
	private int copyId = 0;

	public LoopUnroller(int depth) {
		this.depth = depth;
	}

	@Override
	public void transform(Function function) {
		List<LoopInfo> loops = LoopAnalysis.findLoops(function)
			.stream()
			.filter(l -> l.head.getTerminator() instanceof JumpIfNode)
			.collect(Collectors.toList());

		for (LoopInfo loop : loops) {
			Map<BasicBlock, BasicBlock> loopBlocks = new HashMap<>();
			BasicBlock head = loop.head;
			JumpIfNode headBranch = (JumpIfNode) head.getTerminator();
			BasicBlock headCopy = function.createBlock(head.getName() + "_unrolled_" + this.copyId++);

			head.parents().forEach(parent -> {
				// Rewire the parent terminators into this block
				TerminatorIrNode pTerm = parent.getTerminator();
				if (pTerm instanceof GotoNode) {
					((GotoNode) pTerm).setTarget(headCopy);
				} else if (pTerm instanceof JumpIfNode) {
					JumpIfNode pBranch = (JumpIfNode) pTerm;
					if (pBranch.getThenTarget() == head) {
						pBranch.setThenTarget(headCopy);
					} else {
						pBranch.setElseTarget(headCopy);
					}
 				}
			});

			headCopy.terminate(NodeFactory.JumpIf(headBranch.getCond(), head, headBranch.getElseTarget()));
		}

	}

}
