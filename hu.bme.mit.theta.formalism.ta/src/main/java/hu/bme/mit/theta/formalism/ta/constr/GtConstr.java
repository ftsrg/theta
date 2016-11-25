package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.GtExpr;

public interface GtConstr extends AtomicConstr {

	@Override
	GtExpr toExpr();

}
