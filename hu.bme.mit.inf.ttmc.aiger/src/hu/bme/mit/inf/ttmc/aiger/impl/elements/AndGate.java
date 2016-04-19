package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public final class AndGate extends HWElement {
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
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		Expr<? extends BoolType> expr1 = elements.get(rhs1 / 2).getExpr(elements);
		if (rhs1 % 2 == 1)
			expr1 = Exprs.Not(expr1);

		Expr<? extends BoolType> expr2 = elements.get(rhs2 / 2).getExpr(elements);
		if (rhs2 % 2 == 1)
			expr2 = Exprs.Not(expr2);

		return Exprs.And(ImmutableSet.of(expr1, expr2));
	}

}
