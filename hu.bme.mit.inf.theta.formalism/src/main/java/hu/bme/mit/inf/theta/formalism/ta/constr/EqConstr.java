package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.EqExpr;

public interface EqConstr extends AtomicConstr {

	@Override
	public EqExpr toExpr();

}
