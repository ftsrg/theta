package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public final class OutVar extends HWElement {
	private final int literal;

	public OutVar(final String token) {
		this(Integer.parseInt(token));
	}

	public OutVar(final int literal) {
		super(-1);
		this.literal = literal;
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(literal / 2).getExpr(elements);
		if (literal % 2 == 1)
			expr = Exprs.Not(expr);
		return expr;
	}

	@Override
	public int getVarId() {
		throw new UnsupportedOperationException("OutVars do not have corresponding ID.");
	}

}
