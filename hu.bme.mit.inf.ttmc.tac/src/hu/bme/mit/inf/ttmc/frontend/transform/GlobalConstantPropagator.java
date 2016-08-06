package hu.bme.mit.inf.ttmc.frontend.transform;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Assign;
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.JumpIf;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.dependency.UseDefineChain;
import hu.bme.mit.inf.ttmc.frontend.dependency.UseDefineChain.Definition;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class GlobalConstantPropagator implements FunctionTransformer {

	@Override
	public void transform(Function function) {
		UseDefineChain ud = UseDefineChain.buildChain(function);
		List<BasicBlock> blocks = function.getBlocksDFS().stream()
			.filter(b -> b != function.getExitBlock())
			.collect(Collectors.toList());

		/*
		 * Algorithm for global constant propagation.
		 *
		 * For each constant value definition:
		 * 	1. Find all reachable uses from a definition.
		 * 	2. If there is a use which is only reachable from that single definition, replace its value with a constant.
		 */
		for (BasicBlock block : blocks) {
			// Get all definitions of this block
			List<Definition> defs = ud.getBlockDefines(block).stream()
				.filter(d -> d.node instanceof AssignNode<?, ?>)
				.filter(d -> ((AssignNode<?, ?>) d.node).getExpr() instanceof LitExpr<?>)
				.collect(Collectors.toList());

			// Find all reachable uses from all defs
			defs.forEach(def -> {
				AssignNode<?, ?> assign = (AssignNode<?, ?>) def.node;
				Collection<IrNode> uses = ud.getUses(assign);
				for (IrNode use : uses) {
					// If the use is only reachable from the current def
					Collection<Definition> reachingDefs = ud.getLocalReachingDefinitions(use);
					if (
						reachingDefs.stream().filter(d -> d.var == assign.getVar()).count() == 1
							&&
						reachingDefs.contains(def)
					) {
						Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars = new HashMap<>();
						constVars.put(assign.getVar(), (LitExpr<? extends Type>) assign.getExpr());

						ConstantFolderExprVisitor visitor = new ConstantFolderExprVisitor(constVars);

						if (use instanceof AssignNode<?, ?>) {
							Expr<? extends Type> expr = ((AssignNode<?, ?>) use).getExpr().accept(visitor, null);
							use.getParentBlock().replaceNode(use, Assign(((AssignNode) use).getVar(), expr));
						} else if (use instanceof JumpIfNode) {
							Expr<? extends BoolType> cond = ExprUtils.cast(((JumpIfNode) use).getCond().accept(visitor, null), BoolType.class);
							use.getParentBlock().replaceNode(use, JumpIf(cond, ((JumpIfNode) use).getThenTarget(), ((JumpIfNode) use).getElseTarget()));
						}
					}
				}
			});

		}

	}

}
