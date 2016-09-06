package hu.bme.mit.inf.theta.formalism.ta.constr;

import hu.bme.mit.inf.theta.core.expr.TrueExpr;

public interface TrueConstr extends ClockConstr {

	@Override
	public TrueExpr toExpr();

}
