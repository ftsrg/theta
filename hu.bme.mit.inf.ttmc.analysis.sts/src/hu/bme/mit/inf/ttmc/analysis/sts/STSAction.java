package hu.bme.mit.inf.ttmc.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class STSAction implements Action {

	private final Expr<? extends BoolType> trans;

	public STSAction(final Expr<? extends BoolType> trans) {
		this.trans = checkNotNull(trans);
	}

	public Expr<? extends BoolType> getTrans() {
		return trans;
	}

}
