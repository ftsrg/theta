package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

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
