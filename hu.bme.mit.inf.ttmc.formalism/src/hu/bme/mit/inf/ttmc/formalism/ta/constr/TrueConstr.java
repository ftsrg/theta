package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;

public interface TrueConstr extends Constr {

	@Override
	public TrueExpr asExpr();

}
