package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public interface DiffConstr extends AtomicConstr {

	public ClockDecl getLeftClock();

	public ClockDecl getRightClock();

}
