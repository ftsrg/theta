package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.GeqExpr;

public interface GeqConstr extends AtomicConstr {

	@Override
	GeqExpr toExpr();

}
