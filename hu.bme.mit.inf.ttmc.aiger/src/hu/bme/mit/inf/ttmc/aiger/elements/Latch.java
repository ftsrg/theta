package hu.bme.mit.inf.ttmc.aiger.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public final class Latch extends HWElement {
	private final int nextState;
	private final VarDecl<BoolType> varDecl;

	public Latch(String[] tokens, STSManager manager) {
		this(Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]), manager);
	}
	
	public Latch(int actualState, int nextState, STSManager manager) {
		super(actualState/2);
		this.nextState = nextState;
		varDecl = manager.getDeclFactory().Var("la" + varId, manager.getTypeFactory().Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		return varDecl.getRef();
	}
	
	public Expr<? extends BoolType> getInitExpr(STSManager manager) {
		return manager.getExprFactory().Not(varDecl.getRef());
	}
	
	public Expr<? extends BoolType> getTransExpr(STSManager manager, List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(nextState / 2).getExpr(manager, elements);
		if (nextState % 2 == 1) expr = manager.getExprFactory().Not(expr);
		return manager.getExprFactory().Iff(
				manager.getExprFactory().Prime(varDecl.getRef()),
				expr
				);
	}

}
