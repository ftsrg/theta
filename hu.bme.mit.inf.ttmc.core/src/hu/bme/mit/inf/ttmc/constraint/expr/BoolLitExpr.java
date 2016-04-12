package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface BoolLitExpr extends NullaryExpr<BoolType> {
	public boolean getValue();

}
