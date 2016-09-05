package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.FalseExpr;

public interface FalseConstr extends ClockConstr {

	@Override
	public FalseExpr toExpr();

}
