package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public interface DiffConstr extends AtomicConstr {

	public ClockDecl getLeftClock();

	public ClockDecl getRightClock();

}
