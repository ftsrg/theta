package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;

public interface TrueConstr extends ClockConstr {

	@Override
	public TrueExpr toExpr();

}
