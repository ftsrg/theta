package hu.bme.mit.inf.theta.frontend.transform;

import static hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory.Goto;

import java.util.Optional;

import hu.bme.mit.inf.theta.core.expr.BoolLitExpr;
import hu.bme.mit.inf.theta.core.expr.LitExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode;
import hu.bme.mit.inf.theta.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode.BranchTableEntry;

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
				.filter(block -> {
					if (block.getTerminator() instanceof JumpIfNode && ((JumpIfNode) block.getTerminator()).getCond() instanceof BoolLitExpr) {
						return true;
					}

					if (block.getTerminator() instanceof BranchTableNode) {
						// If the branch table condition is a constant
						return ((BranchTableNode) block.getTerminator()).getCondition() instanceof LitExpr<?>;
					}

					return false;
				})
				.findFirst();

			// If such block exists
			if (result.isPresent()) {
				BasicBlock block = result.get();

				if (block.getTerminator() instanceof JumpIfNode) {
					JumpIfNode terminator = (JumpIfNode) block.getTerminator();
					BoolLitExpr cond = (BoolLitExpr) terminator.getCond();

					BasicBlock target = cond.getValue() == true ? terminator.getThenTarget() : terminator.getElseTarget();

					block.clearTerminator();
					block.terminate(Goto(target));
				} else if (block.getTerminator() instanceof BranchTableNode) {
					BranchTableNode terminator = (BranchTableNode) block.getTerminator();
					LitExpr<? extends Type> cond = (LitExpr<? extends Type>) terminator.getCondition();

					Optional<BranchTableEntry> path = terminator.getValueEntries()
						.stream()
						.filter(entry -> entry.getValue().equals(cond))
						.findFirst();

					BasicBlock target;
					if (path.isPresent()) { // There is a case statement which will be taken always
						target = path.get().getTarget();
					} else { // There is no suitable case statement: The default path will be taken always.
						target = terminator.getDefaultTarget();
					}

					block.clearTerminator();
					block.terminate(Goto(target));
				} else {
					throw new AssertionError("Should not happen.");
				}

				change = true;
			}
		}

		// Eliminate the included orphaned nodes
		function.normalize();
	}

}
