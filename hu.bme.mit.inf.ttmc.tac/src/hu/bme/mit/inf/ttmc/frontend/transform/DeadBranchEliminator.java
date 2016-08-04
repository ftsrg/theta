package hu.bme.mit.inf.ttmc.frontend.transform;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Goto;

public class DeadBranchEliminator implements FunctionTransformer {

	@Override
	public void transform(Function function) {
		List<BasicBlock> blocks = function.getBlocks().stream()
			.filter(b -> b.getTerminator() instanceof JumpIfNode)
			.filter(b -> ((JumpIfNode) b.getTerminator()).getCond() instanceof BoolLitExpr)
			.collect(Collectors.toList());

		for (BasicBlock block : blocks) {
			JumpIfNode terminator = (JumpIfNode) block.getTerminator();
			BoolLitExpr cond = (BoolLitExpr) terminator.getCond();

			BasicBlock target = cond.getValue() == true ? terminator.getThenTarget() : terminator.getElseTarget();
			BasicBlock newBlock = new BasicBlock(block.getName(), function, block.getNodes());

			function.replaceBlock(block, newBlock, Goto(target));
		}
	}

}
