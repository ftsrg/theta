package hu.bme.mit.inf.theta.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.BoolType;

public class FalseConst extends HWElement {

	public FalseConst() {
		super(0);
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		return Exprs.False();
	}

}
