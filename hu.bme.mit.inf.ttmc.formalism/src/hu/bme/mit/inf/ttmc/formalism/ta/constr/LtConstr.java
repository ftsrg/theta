package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.LtExpr;

public interface LtConstr extends AtomicConstr {

	@Override
	public LtExpr toExpr();

}
