package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.core.expr.LtExpr;

public interface LtConstr extends AtomicConstr {

	@Override
	LtExpr toExpr();

}
