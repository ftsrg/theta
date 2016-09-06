package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.LeqExpr;

public interface LeqConstr extends AtomicConstr {

	@Override
	public LeqExpr toExpr();

}
