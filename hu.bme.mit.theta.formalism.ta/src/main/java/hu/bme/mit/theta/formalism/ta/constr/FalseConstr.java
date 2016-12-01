package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.FalseExpr;

public interface FalseConstr extends ClockConstr {

	@Override
	FalseExpr toExpr();

}
