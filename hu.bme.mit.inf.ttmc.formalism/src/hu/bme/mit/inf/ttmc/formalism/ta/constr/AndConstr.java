package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;

public interface AndConstr extends Constr {

	public Collection<? extends AtomicConstr> getConstrs();

	@Override
	public AndExpr asExpr();

}
