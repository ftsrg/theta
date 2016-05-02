package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;

public interface LeqConstr extends AtomicConstr {

	@Override
	public LeqExpr asExpr();

}
