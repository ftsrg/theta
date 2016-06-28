package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.EqExpr;

public interface EqConstr extends AtomicConstr {

	@Override
	public EqExpr toExpr();

}
