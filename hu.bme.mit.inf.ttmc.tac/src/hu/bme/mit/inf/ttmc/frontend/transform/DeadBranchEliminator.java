package hu.bme.mit.inf.ttmc.frontend.transform;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Goto;

/**
 * A function transformer which replaces trivial branches with goto jumps.
 *
 * This transformation may introduce orphaned and split blocks, so a normalization must be run on the resulting graph.
 */
public class DeadBranchEliminator implements FunctionTransformer {

	@Override
	public void transform(Function function) {
		boolean change = true;
		while (change) {
			change = false;

			// Find a suitable basic block
			Optional<BasicBlock> result = function.getBlocksDFS().stream()
				.filter(b -> b.getTerminator() instanceof JumpIfNode)
				.filter(b -> ((JumpIfNode) b.getTerminator()).getCond() instanceof BoolLitExpr)
				.findFirst();

			// If such block exists
			if (result.isPresent()) {
				BasicBlock block = result.get();
				JumpIfNode terminator = (JumpIfNode) block.getTerminator();
				BoolLitExpr cond = (BoolLitExpr) terminator.getCond();

				BasicBlock target = cond.getValue() == true ? terminator.getThenTarget() : terminator.getElseTarget();

				block.clearTerminator();
				block.terminate(Goto(target));

				change = true;
			}
		}
	}

}
