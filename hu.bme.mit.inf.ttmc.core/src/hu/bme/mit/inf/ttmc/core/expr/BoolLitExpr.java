package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface BoolLitExpr extends LitExpr<BoolType>, NullaryExpr<BoolType> {
	public boolean getValue();

}
