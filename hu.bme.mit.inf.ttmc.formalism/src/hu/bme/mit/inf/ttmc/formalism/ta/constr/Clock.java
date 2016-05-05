package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public interface Clock extends Comparable<Clock> {

	public String getName();

	public ClockDecl asDecl();

}
