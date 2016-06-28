package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.GtExpr;

public interface GtConstr extends AtomicConstr {

	@Override
	public GtExpr toExpr();

}
