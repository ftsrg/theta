package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.GeqExpr;

public interface GeqConstr extends AtomicConstr {

	@Override
	public GeqExpr toExpr();

}
