package hu.bme.mit.theta.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.AndExpr;

public interface AndConstr extends ClockConstr {

	Collection<? extends AtomicConstr> getConstrs();

	@Override
	AndExpr toExpr();

}
