package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.LtExpr;

public interface LtConstr extends AtomicConstr {

	@Override
	public LtExpr toExpr();

}
