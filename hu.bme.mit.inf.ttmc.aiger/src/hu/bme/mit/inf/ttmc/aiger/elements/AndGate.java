package hu.bme.mit.inf.ttmc.aiger.elements;

import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public final class AndGate extends HWElement {
	private final int rhs1, rhs2;
	
	public AndGate(String[] tokens) {
		this(Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]), Integer.parseInt(tokens[2]));
	}
	
	public AndGate(int lhs, int rhs1, int rhs2) {
		super(lhs/2);
		this.rhs1 = rhs1;
		this.rhs2 = rhs2;
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		Expr<? extends BoolType> expr1 = elements.get(rhs1/2).getExpr(manager, elements);
		if (rhs1 % 2 == 1) expr1 = manager.getExprFactory().Not(expr1);
		
		Expr<? extends BoolType> expr2 = elements.get(rhs2/2).getExpr(manager, elements);
		if (rhs2 % 2 == 1) expr2 = manager.getExprFactory().Not(expr2);
		
		return manager.getExprFactory().And(ImmutableSet.of(expr1, expr2));
	}

}
