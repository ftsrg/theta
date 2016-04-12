package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public class FalseConst extends HWElement {

	public FalseConst() {
		super(0);
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		return manager.getExprFactory().False();
	}

}
