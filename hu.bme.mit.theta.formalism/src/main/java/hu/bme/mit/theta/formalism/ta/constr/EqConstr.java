package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.EqExpr;

public interface EqConstr extends AtomicConstr {

	@Override
	public EqExpr toExpr();

}
