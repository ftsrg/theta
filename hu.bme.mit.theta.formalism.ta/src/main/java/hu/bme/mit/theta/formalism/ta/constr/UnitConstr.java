package hu.bme.mit.theta.formalism.ta.constr;

import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public interface UnitConstr extends AtomicConstr {

	ClockDecl getClock();

}
