package hu.bme.mit.inf.ttmc.aiger.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public final class OutVar extends HWElement {
	private final int literal;
	
	public OutVar(String token) {
		this(Integer.parseInt(token));
	}
	
	public OutVar(int literal) {
		super(-1);
		this.literal = literal;
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(literal / 2).getExpr(manager, elements);
		if (literal % 2 == 1) expr = manager.getExprFactory().Not(expr);
		return expr;
	}
	
	@Override
	public int getVarId() {
		throw new UnsupportedOperationException("OutVars do not have corresponding ID.");
	}

}
