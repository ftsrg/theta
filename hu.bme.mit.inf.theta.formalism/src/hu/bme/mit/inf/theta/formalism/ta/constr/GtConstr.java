package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.GtExpr;

public interface GtConstr extends AtomicConstr {

	@Override
	public GtExpr toExpr();

}
