package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface BoolLitExpr extends NullaryExpr<BoolType> {
	public boolean getValue();

}
