package hu.bme.mit.inf.ttmc.aiger.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public abstract class HWElement {
	protected int varId;
	
	public HWElement(int varId) {
		this.varId = varId;
	}
	
	public abstract Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements);
	
	public int getVarId() {
		return varId;
	}
}
