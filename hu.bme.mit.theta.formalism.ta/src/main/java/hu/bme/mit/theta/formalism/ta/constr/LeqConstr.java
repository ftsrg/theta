package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.LeqExpr;

public interface LeqConstr extends AtomicConstr {

	@Override
	public LeqExpr toExpr();

}
