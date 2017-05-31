package hu.bme.mit.theta.frontend.aiger.impl.elements;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class AndGate extends HwElement {
	private final int rhs1, rhs2;

	public AndGate(final String[] tokens) {
		this(Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]), Integer.parseInt(tokens[2]));
	}

	public AndGate(final int lhs, final int rhs1, final int rhs2) {
		super(lhs / 2);
		this.rhs1 = rhs1;
		this.rhs2 = rhs2;
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HwElement> elements) {
		Expr<? extends BoolType> expr1 = elements.get(rhs1 / 2).getExpr(elements);
		if (rhs1 % 2 != 0)
			expr1 = Not(expr1);

		Expr<? extends BoolType> expr2 = elements.get(rhs2 / 2).getExpr(elements);
		if (rhs2 % 2 != 0)
			expr2 = Not(expr2);

		return And(expr1, expr2);
	}

}
