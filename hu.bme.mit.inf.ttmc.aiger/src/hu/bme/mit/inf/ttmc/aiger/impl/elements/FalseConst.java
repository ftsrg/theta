package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class FalseConst extends HWElement {

	public FalseConst() {
		super(0);
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		return Exprs.False();
	}

}
