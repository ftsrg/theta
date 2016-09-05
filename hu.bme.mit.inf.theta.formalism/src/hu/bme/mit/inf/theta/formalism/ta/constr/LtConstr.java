package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.LtExpr;

public interface LtConstr extends AtomicConstr {

	@Override
	public LtExpr toExpr();

}
