package hu.bme.mit.theta.frontend.c.transform;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain.Definition;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.AssertNode;
import hu.bme.mit.theta.frontend.c.ir.node.AssignNode;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.transform.expr.ConstantFolderExprVisitor;

public class ConstantPropagator extends FunctionTransformer {

	@Override
	public void transform(Function function) {
		UseDefineChain ud = UseDefineChain.buildChain(function);
		List<BasicBlock> blocks = function.getBlocksDFS().stream().filter(b -> b != function.getExitBlock())
				.collect(Collectors.toList());

		for (BasicBlock block : blocks) {
			Set<Definition> defs = ud.getReachingDefinitions(block);
			Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars = new HashMap<>();
			ConstantFolderExprVisitor visitor = new ConstantFolderExprVisitor(constVars);

			defs.stream()
					// The reaching definition is an assignment
					.filter(b -> b.node instanceof AssignNode<?, ?>)
					// With a literal value
					.filter(b -> ((AssignNode<?, ?>) b.node).getExpr() instanceof LitExpr<?>)
					// and it is the only reaching definition of its variable
					.filter(b -> defs.stream().noneMatch(d -> d != b && d.var == b.var)).forEach(
						b -> constVars.put(b.var, (LitExpr<? extends Type>) ((AssignNode<?, ?>) b.node).getExpr())
					);

			for (IrNode node : block.getAllNodes()) {
				if (node instanceof AssignNode<?, ?>) {
					@SuppressWarnings("unchecked")
					AssignNode<? extends Type, ? extends Type> assign = (AssignNode<? extends Type, ? extends Type>) node;
					this.transformAssign(assign, visitor);
				} else if (node instanceof JumpIfNode) {
					JumpIfNode jump = (JumpIfNode) node;
					Expr<? extends BoolType> expr = ExprUtils.cast(jump.getCondition().accept(visitor, null),
							BoolType.class);

					jump.setCondition(expr);
				} else if (node instanceof AssertNode) {
					AssertNode assrt = (AssertNode) node;
					Expr<? extends BoolType> expr = ExprUtils.cast(assrt.getCond().accept(visitor, null),
							BoolType.class);

					assrt.setCond(expr);
				} else if (node instanceof BranchTableNode) {
					BranchTableNode branch = (BranchTableNode) node;
					Expr<? extends Type> expr = branch.getCondition().accept(visitor, null);

					branch.setCondition(expr);
				}
			}
		}
	}

	@SuppressWarnings("unchecked")
	private <VarType extends Type, ExprType extends VarType> void transformAssign(AssignNode<VarType, ExprType> assign,
			ConstantFolderExprVisitor visitor) {
		Expr<? extends Type> expr = assign.getExpr().accept(visitor, null);

		if (expr instanceof LitExpr<?>) {
			// It is a constant, we can save it
			visitor.getConstVars().put(assign.getVar(), (LitExpr<?>) expr);
		} else {
			// It does not contain a constant value, so it should not be present
			// in the map
			visitor.getConstVars().remove(assign.getVar());
		}

		assign.setExpr(expr);
	}

	@Override
	public String getTransformationName() {
		return "ConstantPropagation";
	}

}
