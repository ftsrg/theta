package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.TrueExpr;

public interface TrueConstr extends ClockConstr {

	@Override
	public TrueExpr toExpr();

}
