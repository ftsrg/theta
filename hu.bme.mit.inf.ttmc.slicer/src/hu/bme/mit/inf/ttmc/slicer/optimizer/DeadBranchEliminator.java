package hu.bme.mit.inf.ttmc.slicer.optimizer;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.slicer.cfg.BlockCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.BranchingBlockCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class DeadBranchEliminator implements CFGOptimizer {

	@Override
	public CFG transform(CFG input) {

		List<CFGNode> inputNodes = input.nodes();

		inputNodes.stream().filter(s -> s instanceof BranchingBlockCFGNode).forEach(node -> {
			BranchingBlockCFGNode branch = (BranchingBlockCFGNode) node;

			// FIXME: Is this always a safe cast?
			AssumeStmt assume = (AssumeStmt) branch.getBranchNode().getStmt();
			Expr<? extends BoolType> cond = assume.getCond();
			if (cond instanceof BoolLitExpr) {
				boolean val = ((BoolLitExpr) cond).getValue();

				// If the value is true, we need to remove the false branch
				if (val == true) {
					branch.getElseNode().removeParent(branch);
				} else {
					branch.getThenNode().removeParent(branch);
				}

				// We no longer need the assume node
				List<StmtCFGNode> nodes = branch.getContainedNodes();
				StmtCFGNode branchNode = nodes.get(nodes.size() - 1);
				branchNode.remove();
				nodes.remove(nodes.size() - 1);

				BlockCFGNode block = new BlockCFGNode(nodes);
				branch.replace(block);
			}
		});

		// We need to clean up orphaned nodes
		List<CFGNode> visited = GraphAlgorithm.DFS(input.getEntry());

		inputNodes.forEach(s -> {
			if (!visited.contains(s)) {
				s.getParents().forEach(p -> p.getChildren().remove(s));
				s.getChildren().forEach(c -> c.getParents().remove(s));
			}
		});

		return input;
	}

}
