package hu.bme.mit.inf.ttmc.frontend.transform;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Assign;
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.JumpIf;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class LocalConstantPropagator implements FunctionTransformer {

	@Override
	public void transform(Function function) {
		List<BasicBlock> blocks = new ArrayList<>(function.getBlocks());
		for (BasicBlock block : blocks) {
			if (function.getExitBlock() == block)
				continue;

			this.transformBlock(function, block);
		}
	}

	@SuppressWarnings("unchecked")
	private void transformBlock(Function function, BasicBlock block) {
		Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars = new HashMap<>();
		ConstantFolderExprVisitor visitor = new ConstantFolderExprVisitor(constVars);
		List<NonTerminatorIrNode> nodes = new ArrayList<>(block.getNodes());
		TerminatorIrNode terminator = block.getTerminator();

		block.clearNodes();
		block.clearTerminator();
		/* Propagate through the assignments */
		for (NonTerminatorIrNode node : nodes) {
			if (node instanceof AssignNode<?, ?>) {
				AssignNode<? extends Type, ? extends Type> assign = (AssignNode<? extends Type, ? extends Type>) node;
				Expr<? extends Type> expr = assign.getExpr().accept(visitor, null);

				if (expr instanceof LitExpr<?>) {
					// It is a constant, we can save it
					constVars.put(assign.getVar(), (LitExpr<?>) expr);
				} else {
					// It does not contain a constant value, so it should not be present in the map
					constVars.remove(assign.getVar());
				}

				if (expr != assign.getExpr()) {
					block.addNode(Assign(assign.getVar(), ExprUtils.cast(expr, assign.getVar().getType().getClass())));
				} else {
					block.addNode(node);
				}
			}
		}


		/* Check whether we have conditional terminator as well */
		if (block.getTerminator() instanceof JumpIfNode) {
			JumpIfNode jump = (JumpIfNode) block.getTerminator();
			Expr<? extends BoolType> expr = ExprUtils.cast(jump.getCond().accept(visitor, null), BoolType.class);

			terminator = JumpIf(expr, jump.getThenTarget(), jump.getElseTarget());
		}

		block.terminate(terminator);
	}

}
