package hu.bme.mit.theta.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.AndExpr;

public interface AndConstr extends ClockConstr {

	public Collection<? extends AtomicConstr> getConstrs();

	@Override
	public AndExpr toExpr();

}
