package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;

public interface FalseConstr extends ClockConstr {

	@Override
	public FalseExpr toExpr();

}
