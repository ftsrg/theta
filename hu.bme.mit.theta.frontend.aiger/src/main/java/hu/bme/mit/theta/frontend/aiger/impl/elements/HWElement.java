package hu.bme.mit.theta.frontend.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public abstract class HWElement {
	protected int varId;

	public HWElement(final int varId) {
		this.varId = varId;
	}

	public abstract Expr<? extends BoolType> getExpr(List<HWElement> elements);

	public int getVarId() {
		return varId;
	}
}
