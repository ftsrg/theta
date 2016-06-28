package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;

public interface GeqConstr extends AtomicConstr {

	@Override
	public GeqExpr toExpr();

}
