package hu.bme.mit.inf.ttmc.analysis.sts;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class STSAction implements Action {

	final Expr<? extends BoolType> trans;

	STSAction(final Expr<? extends BoolType> trans) {
		this.trans = trans;
	}

	public Expr<? extends BoolType> getTrans() {
		return trans;
	}

}
